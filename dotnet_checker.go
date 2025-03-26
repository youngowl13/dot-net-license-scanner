package main

import (
	"encoding/json"
	"encoding/xml"
	"fmt"
	"io/fs"
	"io/ioutil"
	"log"
	"net/http"
	"os"
	"path/filepath"
	"sort"
	"strings"
	"sync"
)

// PackageReference represents a NuGet package reference in the csproj.
type PackageReference struct {
	XMLName xml.Name `xml:"PackageReference"`
	Include string   `xml:"Include,attr"`
	Version string   `xml:"Version,attr"`
}

// Project represents a simplified csproj file structure.
type Project struct {
	XMLName    xml.Name `xml:"Project"`
	ItemGroups []struct {
		PackageReferences []PackageReference `xml:"PackageReference"`
	} `xml:"ItemGroup"`
}

// Dependency represents a dependency from NuGet metadata.
type Dependency struct {
	Id    string `json:"id"`
	Range string `json:"range"`
}

// DependencyGroup holds dependency details for a given target framework.
type DependencyGroup struct {
	TargetFramework string       `json:"targetFramework"`
	Dependencies    []Dependency `json:"dependencies"`
}

// CatalogEntry holds the package metadata from NuGet.
type CatalogEntry struct {
	Version           string            `json:"version"`
	LicenseExpression string            `json:"licenseExpression"`
	LicenseURL        string            `json:"licenseUrl"`
	DependencyGroups  []DependencyGroup `json:"dependencyGroups"`
}

// NuGetRegistration represents the JSON structure returned by NuGet's registration API.
type NuGetRegistration struct {
	Items []struct {
		Items []struct {
			CatalogEntry CatalogEntry `json:"catalogEntry"`
		} `json:"items"`
	} `json:"items"`
}

// PackageReport holds the result of scanning a package.
type PackageReport struct {
	PackageID         string
	Version           string
	LicenseExpression string
	LicenseURL        string
	IsCopyleft        bool
	DebugMessages     []string
	Dependencies      []*PackageReport
	Level             int      // 0 = direct dependency, >0 = transitive
	IntroducedBy      []string // Top-level csproj file(s) that introduced this package.
}

// Summary holds overall scan statistics.
type Summary struct {
	TotalPackages      int
	DirectPackages     int
	TransitivePackages int
	CopyleftPackages   int
	ErrorCount         int
}

// -----------------------------------------------------------------------------
// 1) CONCURRENCY CONTROL
// -----------------------------------------------------------------------------

// We'll use a semaphore (channel) to limit concurrency to 20 goroutines.
var concurrencySem = make(chan struct{}, 20)

// acquireSemaphore waits for capacity in the concurrencySem.
func acquireSemaphore() {
	concurrencySem <- struct{}{}
}

// releaseSemaphore frees up capacity in the concurrencySem.
func releaseSemaphore() {
	<-concurrencySem
}

// -----------------------------------------------------------------------------
// 2) VERSION NORMALIZATION
// -----------------------------------------------------------------------------

// normalizeVersion removes trailing ".0" segments. For example:
//   "4.0.0.0" -> "4.0.0"
//   "1.2.3.0" -> "1.2.3"
//   "2.0.0"   -> "2.0"
//   "5.0"     -> "5.0" (unchanged, because only one trailing zero)
func normalizeVersion(ver string) string {
	if ver == "" {
		return ""
	}
	parts := strings.Split(ver, ".")
	// Always keep at least 1 segment
	for len(parts) > 1 && parts[len(parts)-1] == "0" {
		parts = parts[:len(parts)-1]
	}
	return strings.Join(parts, ".")
}

// -----------------------------------------------------------------------------
// 3) SKIP KNOWN .NET FRAMEWORK ASSEMBLIES
// -----------------------------------------------------------------------------

// skipFrameworkAssembly returns true if the package should be ignored
// because it's a known .NET framework assembly (e.g. "System.*", "Microsoft.Win32.*").
func skipFrameworkAssembly(packageID string) bool {
	idLower := strings.ToLower(packageID)
	return strings.HasPrefix(idLower, "system.") ||
		strings.HasPrefix(idLower, "microsoft.win32.")
}

// -----------------------------------------------------------------------------
// 4) REPORT AND SCANNING LOGIC
// -----------------------------------------------------------------------------

// getCssClass returns the CSS class for a package report based on its license.
func getCssClass(rep *PackageReport) string {
	if rep.IsCopyleft {
		return "copyleft"
	}
	if rep.LicenseExpression == "" {
		return "unknown"
	}
	return "non-copyleft"
}

// toHTML converts a PackageReport (and its children) to an HTML nested list.
func (r *PackageReport) toHTML() string {
	cssClass := getCssClass(r)
	var sb strings.Builder
	sb.WriteString(fmt.Sprintf("<li class=\"%s\">", cssClass))
	sb.WriteString(fmt.Sprintf("<strong>%s@%s</strong> ", r.PackageID, r.Version))
	sb.WriteString(fmt.Sprintf("License: %s", r.LicenseExpression))
	if r.LicenseURL != "" {
		sb.WriteString(fmt.Sprintf(" (<a href=\"%s\">License URL</a>)", r.LicenseURL))
	}
	if r.Level > 0 && len(r.IntroducedBy) > 0 {
		sb.WriteString(fmt.Sprintf("<br/><em>Introduced by: %s</em>", strings.Join(r.IntroducedBy, ", ")))
	}
	// Include debug messages.
	if len(r.DebugMessages) > 0 {
		sb.WriteString("<br/><details><summary>Debug Messages</summary><ul class=\"debug\">")
		for _, msg := range r.DebugMessages {
			sb.WriteString(fmt.Sprintf("<li>%s</li>", msg))
		}
		sb.WriteString("</ul></details>")
	}
	// Process children.
	if len(r.Dependencies) > 0 {
		sb.WriteString("<ul>")
		for _, child := range r.Dependencies {
			sb.WriteString(child.toHTML())
		}
		sb.WriteString("</ul>")
	}
	sb.WriteString("</li>")
	return sb.String()
}

// isCopyleft returns true if the license string indicates a copyleft license.
func isCopyleft(license string) bool {
	copyleftLicenses := []string{"GPL-2.0", "GPL-3.0", "LGPL-2.1", "LGPL-3.0", "AGPL-3.0"}
	for _, cl := range copyleftLicenses {
		if strings.Contains(strings.ToUpper(license), strings.ToUpper(cl)) {
			return true
		}
	}
	return false
}

// parseVersionFromRange extracts a version from a dependency range string.
// For example, "[1.2.3, )" returns "1.2.3".
func parseVersionFromRange(rangeStr string) string {
	if rangeStr == "" {
		return ""
	}
	if rangeStr[0] == '[' || rangeStr[0] == '(' {
		endIndex := strings.IndexAny(rangeStr, ",)]")
		if endIndex > 1 {
			return rangeStr[1:endIndex]
		}
	}
	return rangeStr
}

// getPackageInfo queries the NuGet registration API for a given package ID and version.
// If version is empty, it picks the latest version from the registration data.
func getPackageInfo(packageID, version string) (string, string, []DependencyGroup, error) {
	url := fmt.Sprintf("https://api.nuget.org/v3/registration5-semver1/%s/index.json", strings.ToLower(packageID))
	resp, err := http.Get(url)
	if err != nil {
		return "", "", nil, fmt.Errorf("failed to get package info: %w", err)
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return "", "", nil, fmt.Errorf("received non-OK HTTP status: %s", resp.Status)
	}
	body, err := ioutil.ReadAll(resp.Body)
	if err != nil {
		return "", "", nil, fmt.Errorf("failed to read response body: %w", err)
	}
	var reg NuGetRegistration
	if err := json.Unmarshal(body, &reg); err != nil {
		return "", "", nil, fmt.Errorf("failed to unmarshal JSON: %w", err)
	}

	// If version is empty, choose the latest version available.
	if version == "" {
		if len(reg.Items) == 0 {
			return "", "", nil, fmt.Errorf("no registration items for package %s", packageID)
		}
		lastPage := reg.Items[len(reg.Items)-1]
		if len(lastPage.Items) == 0 {
			return "", "", nil, fmt.Errorf("no items in the last registration page for package %s", packageID)
		}
		entry := lastPage.Items[len(lastPage.Items)-1].CatalogEntry
		return entry.LicenseExpression, entry.LicenseURL, entry.DependencyGroups, nil
	}

	// Otherwise, look for the specified version.
	for _, page := range reg.Items {
		for _, item := range page.Items {
			entry := item.CatalogEntry
			if entry.Version == version {
				return entry.LicenseExpression, entry.LicenseURL, entry.DependencyGroups, nil
			}
		}
	}
	return "", "", nil, fmt.Errorf("version %s not found for package %s", version, packageID)
}

// containsString checks if a slice contains a given string.
func containsString(slice []string, s string) bool {
	for _, item := range slice {
		if item == s {
			return true
		}
	}
	return false
}

// processPackage recursively processes a package and its dependencies using concurrency.
func processPackage(
	packageID, version string,
	visited map[string]*PackageReport,
	level int,
	indent string,
	topLevels []string,
	wg *sync.WaitGroup,
	visitedMu *sync.Mutex,
) *PackageReport {
	defer wg.Done()

	// Concurrency limit: wait for a token before proceeding.
	acquireSemaphore()
	defer releaseSemaphore()

	// Skip known framework assemblies (e.g., "System.*", "Microsoft.Win32.*").
	if skipFrameworkAssembly(packageID) {
		fmt.Printf("%sSkipping framework assembly: %s\n", indent, packageID)
		return nil
	}

	// Normalize the version for the visited key, but still use the original version
	// when calling getPackageInfo.
	normVersion := normalizeVersion(version)
	key := packageID + "@" + normVersion

	if level == 0 && len(topLevels) == 0 {
		topLevels = []string{packageID}
	}

	visitedMu.Lock()
	if existing, found := visited[key]; found {
		for _, t := range topLevels {
			if !containsString(existing.IntroducedBy, t) {
				existing.IntroducedBy = append(existing.IntroducedBy, t)
				existing.DebugMessages = append(existing.DebugMessages, fmt.Sprintf("Re-encountered via topLevels: %v", topLevels))
			}
		}
		visitedMu.Unlock()
		fmt.Printf("%sAlready processed package %s@%s, updating IntroducedBy.\n", indent, packageID, normVersion)
		return existing
	}

	// If no version is specified, display "unknown".
	displayVersion := version
	if displayVersion == "" {
		displayVersion = "unknown"
	}

	report := &PackageReport{
		PackageID:     packageID,
		Version:       displayVersion,
		Level:         level,
		IntroducedBy:  append([]string{}, topLevels...),
		DebugMessages: []string{fmt.Sprintf("Processing package %s@%s at level %d", packageID, normVersion, level)},
	}
	visited[key] = report
	visitedMu.Unlock()

	fmt.Printf("%sProcessing package: %s@%s\n", indent, packageID, normVersion)
	license, licenseURL, depGroups, err := getPackageInfo(packageID, version)
	if err != nil {
		errMsg := fmt.Sprintf("Error retrieving license info: %v", err)
		fmt.Printf("%s%s\n", indent, errMsg)
		report.DebugMessages = append(report.DebugMessages, errMsg)
		return report
	}
	report.LicenseExpression = license
	report.LicenseURL = licenseURL
	if isCopyleft(license) {
		report.IsCopyleft = true
	}
	report.DebugMessages = append(report.DebugMessages, fmt.Sprintf("Retrieved license: %s", license))
	fmt.Printf("%sLicense: %s\n", indent, license)

	var childWg sync.WaitGroup
	var childMu sync.Mutex

	for _, group := range depGroups {
		if len(group.Dependencies) > 0 {
			groupMsg := fmt.Sprintf("Processing dependency group for target framework: %s", group.TargetFramework)
			report.DebugMessages = append(report.DebugMessages, groupMsg)
			fmt.Printf("%s%s\n", indent, groupMsg)

			for _, dep := range group.Dependencies {
				depVersion := parseVersionFromRange(dep.Range)
				if depVersion == "" {
					msg := fmt.Sprintf("No version specified for dependency %s, skipping.", dep.Id)
					fmt.Printf("%s%s\n", indent, msg)
					report.DebugMessages = append(report.DebugMessages, msg)
					continue
				}
				fmt.Printf("%sResolving dependency: %s@%s\n", indent, dep.Id, depVersion)

				childWg.Add(1)
				go func(depID, depVer, childIndent string, childTopLevels []string) {
					defer childWg.Done()
					wg.Add(1) // Because each child also defers wg.Done() inside processPackage
					childReport := processPackage(depID, depVer, visited, level+1, childIndent, childTopLevels, wg, visitedMu)
					if childReport != nil {
						childMu.Lock()
						report.Dependencies = append(report.Dependencies, childReport)
						childMu.Unlock()
					}
				}(dep.Id, depVersion, indent+"    ", topLevels)
			}
		}
	}

	childWg.Wait()
	return report
}

// flattenBFS returns a slice of PackageReports in breadth-first order.
func flattenBFS(reports []*PackageReport) []*PackageReport {
	var result []*PackageReport
	queue := make([]*PackageReport, 0)
	queue = append(queue, reports...)
	for len(queue) > 0 {
		current := queue[0]
		queue = queue[1:]
		result = append(result, current)
		queue = append(queue, current.Dependencies...)
	}
	return result
}

// getLicensePriority returns an integer representing license priority.
// 0 = copyleft (red), 1 = unknown (yellow), 2 = non-copyleft (green).
func getLicensePriority(rep *PackageReport) int {
	if rep.IsCopyleft {
		return 0
	}
	if rep.LicenseExpression == "" {
		return 1
	}
	return 2
}

// generateHTMLReport produces an HTML report with a summary, nested tree view,
// and a BFS table view. The Info URL column links to NuGet if license is known,
// otherwise it links to a Google search query.
func generateHTMLReport(reports []*PackageReport) string {
	summary := Summary{}
	flat := flattenBFS(reports)

	// Sort flat list by license priority: red (0) first, then yellow (1), then green (2)
	sort.Slice(flat, func(i, j int) bool {
		return getLicensePriority(flat[i]) < getLicensePriority(flat[j])
	})

	summary.TotalPackages = len(flat)
	for _, rep := range flat {
		if rep.Level == 0 {
			summary.DirectPackages++
		} else {
			summary.TransitivePackages++
		}
		if rep.IsCopyleft {
			summary.CopyleftPackages++
		}
		for _, msg := range rep.DebugMessages {
			if strings.Contains(msg, "Error") {
				summary.ErrorCount++
				break
			}
		}
	}

	var sb strings.Builder
	sb.WriteString("<html><head><title>Copyleft Scan Report</title>")
	sb.WriteString("<style>")
	sb.WriteString("body { font-family: Arial, sans-serif; }")
	sb.WriteString(".copyleft { color: red; font-weight: bold; }")
	sb.WriteString(".unknown { color: orange; font-weight: bold; }")
	sb.WriteString(".non-copyleft { color: green; font-weight: bold; }")
	sb.WriteString(".debug { font-size: 0.8em; color: #888; }")
	sb.WriteString("table, th, td { border: 1px solid #ccc; border-collapse: collapse; padding: 5px; }")
	sb.WriteString("th { background-color: #f0f0f0; }")
	sb.WriteString("ul { list-style-type: none; }")
	sb.WriteString("details summary { cursor: pointer; }")
	sb.WriteString("</style>")
	sb.WriteString("</head><body>")

	sb.WriteString("<h1>Copyleft Scan Report</h1>")
	// Summary Section
	sb.WriteString("<h2>Summary</h2>")
	sb.WriteString("<ul>")
	sb.WriteString(fmt.Sprintf("<li>Total Packages Scanned: %d</li>", summary.TotalPackages))
	sb.WriteString(fmt.Sprintf("<li>Direct Packages: %d</li>", summary.DirectPackages))
	sb.WriteString(fmt.Sprintf("<li>Transitive Packages: %d</li>", summary.TransitivePackages))
	sb.WriteString(fmt.Sprintf("<li>Copyleft Packages: %d</li>", summary.CopyleftPackages))
	sb.WriteString(fmt.Sprintf("<li>Errors Encountered: %d</li>", summary.ErrorCount))
	sb.WriteString("</ul>")

	// Nested Tree View
	sb.WriteString("<h2>Dependency Tree (Nested View)</h2>")
	sb.WriteString("<ul>")
	for _, report := range reports {
		sb.WriteString(report.toHTML())
	}
	sb.WriteString("</ul>")

	// BFS Table View
	sb.WriteString("<h2>Dependency List (BFS Order)</h2>")
	sb.WriteString("<table>")
	sb.WriteString("<tr><th>Level</th><th>Package</th><th>Version</th><th>License</th><th>Info URL</th><th>Introduced By</th><th>Debug Info</th></tr>")
	for _, rep := range flat {
		cssClass := getCssClass(rep)
		sb.WriteString(fmt.Sprintf("<tr class=\"%s\">", cssClass))
		sb.WriteString(fmt.Sprintf("<td>%d</td>", rep.Level))
		sb.WriteString(fmt.Sprintf("<td>%s</td>", rep.PackageID))
		sb.WriteString(fmt.Sprintf("<td>%s</td>", rep.Version))
		sb.WriteString(fmt.Sprintf("<td>%s</td>", rep.LicenseExpression))

		// Info URL: If license is known, link to NuGet; else link to Google search.
		var infoURL string
		if rep.LicenseExpression != "" {
			infoURL = fmt.Sprintf("https://www.nuget.org/packages/%s", rep.PackageID)
		} else {
			infoURL = fmt.Sprintf("https://www.google.com/search?q=%s", rep.PackageID)
		}
		sb.WriteString(fmt.Sprintf("<td><a href=\"%s\">Link</a></td>", infoURL))

		intro := "N/A"
		if len(rep.IntroducedBy) > 0 {
			intro = strings.Join(rep.IntroducedBy, ", ")
		}
		sb.WriteString(fmt.Sprintf("<td>%s</td>", intro))

		debugInfo := strings.Join(rep.DebugMessages, " | ")
		sb.WriteString(fmt.Sprintf("<td>%s</td>", debugInfo))
		sb.WriteString("</tr>")
	}
	sb.WriteString("</table>")

	sb.WriteString("</body></html>")
	return sb.String()
}

// findCsprojFiles recursively finds all .csproj files starting from rootPath.
func findCsprojFiles(rootPath string) ([]string, error) {
	var files []string
	err := filepath.WalkDir(rootPath, func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if !d.IsDir() && strings.HasSuffix(strings.ToLower(d.Name()), ".csproj") {
			files = append(files, path)
		}
		return nil
	})
	return files, err
}

func main() {
	// Fixed defaults: search current directory, produce "report.html"
	rootPath := "."
	outHTML := "report.html"

	info, err := os.Stat(rootPath)
	if err != nil {
		log.Fatalf("Failed to stat path: %v", err)
	}
	var csprojFiles []string
	if info.IsDir() {
		csprojFiles, err = findCsprojFiles(rootPath)
		if err != nil {
			log.Fatalf("Failed to search for csproj files: %v", err)
		}
		if len(csprojFiles) == 0 {
			log.Fatalf("No csproj files found in directory %s", rootPath)
		}
	} else {
		csprojFiles = []string{rootPath}
	}

	visited := make(map[string]*PackageReport)
	var visitedMu sync.Mutex
	var wg sync.WaitGroup
	var reportsMu sync.Mutex
	var reports []*PackageReport

	for _, file := range csprojFiles {
		data, err := ioutil.ReadFile(file)
		if err != nil {
			log.Printf("Failed to read %s: %v", file, err)
			continue
		}
		var proj Project
		if err := xml.Unmarshal(data, &proj); err != nil {
			log.Printf("Failed to parse %s: %v", file, err)
			continue
		}
		topLevelID := filepath.Base(file)

		for _, group := range proj.ItemGroups {
			for _, pkg := range group.PackageReferences {
				wg.Add(1)
				go func(pkg PackageReference, topID string) {
					defer func() {
						// If the goroutine panics or returns, ensure we don't leak the WaitGroup.
						// (Though the concurrencySem is also handled within processPackage).
					}()
					rep := processPackage(pkg.Include, pkg.Version, visited, 0, "", []string{topID}, &wg, &visitedMu)
					if rep != nil {
						reportsMu.Lock()
						reports = append(reports, rep)
						reportsMu.Unlock()
					}
				}(pkg, topLevelID)
			}
		}
	}

	wg.Wait()

	htmlReport := generateHTMLReport(reports)
	if err := ioutil.WriteFile(outHTML, []byte(htmlReport), 0644); err != nil {
		log.Fatalf("Failed to write HTML report: %v", err)
	}
	fmt.Printf("HTML report generated: %s\n", outHTML)
}
