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

// PackageReference represents a NuGet package reference in a csproj.
type PackageReference struct {
	XMLName xml.Name `xml:"PackageReference"`
	Include string   `xml:"Include,attr"` // e.g., "AutoMapper"
	Version string   `xml:"Version,attr"` // e.g., "12.0.1"
}

// Project represents a simplified csproj file structure.
type Project struct {
	XMLName    xml.Name `xml:"Project"`
	ItemGroups []struct {
		PackageReferences []PackageReference `xml:"PackageReference"`
	} `xml:"ItemGroup"`
}

// Dependency from NuGet metadata.
type Dependency struct {
	Id    string `json:"id"`
	Range string `json:"range"`
}

// DependencyGroup from NuGet metadata.
type DependencyGroup struct {
	TargetFramework string       `json:"targetFramework"`
	Dependencies    []Dependency `json:"dependencies"`
}

// CatalogEntry from NuGet metadata.
type CatalogEntry struct {
	Version           string            `json:"version"`
	LicenseExpression string            `json:"licenseExpression"`
	LicenseURL        string            `json:"licenseUrl"`
	DependencyGroups  []DependencyGroup `json:"dependencyGroups"`
}

// NuGetRegistration from NuGet metadata.
type NuGetRegistration struct {
	Items []struct {
		Items []struct {
			CatalogEntry CatalogEntry `json:"catalogEntry"`
		} `json:"items"`
	} `json:"items"`
}

// PackageReport is what we show in the final report.
type PackageReport struct {
	PackageID         string           // e.g., "AutoMapper"
	Version           string           // e.g., "12.0.1" or "unknown"
	LicenseExpression string           // e.g., "MIT"
	LicenseURL        string           // e.g., "https://licenses.nuget.org/MIT"
	IsCopyleft        bool
	Dependencies      []*PackageReport // children
	Level             int      // 0 = direct dependency, >0 = transitive
	IntroducedBy      []string // direct dependency names that introduced this package
}

// Summary holds combined statistics across all files.
type Summary struct {
	TotalPackages      int
	DirectPackages     int
	TransitivePackages int
	CopyleftPackages   int
	ErrorCount         int
}

// ----------------------------------------------------------------------------
// CONCURRENCY LIMIT (20 GOROUTINES)
// ----------------------------------------------------------------------------

var concurrencySem = make(chan struct{}, 20)

func acquireSemaphore() {
	concurrencySem <- struct{}{}
}

func releaseSemaphore() {
	<-concurrencySem
}

// ----------------------------------------------------------------------------
// VERSION NORMALIZATION
// ----------------------------------------------------------------------------

// normalizeVersion removes trailing ".0" segments, e.g. "4.0.0.0" -> "4.0.0"
func normalizeVersion(ver string) string {
	if ver == "" {
		return ""
	}
	parts := strings.Split(ver, ".")
	for len(parts) > 1 && parts[len(parts)-1] == "0" {
		parts = parts[:len(parts)-1]
	}
	return strings.Join(parts, ".")
}

// ----------------------------------------------------------------------------
// SKIP .NET FRAMEWORK ASSEMBLIES
// ----------------------------------------------------------------------------

func skipFrameworkAssembly(packageID string) bool {
	idLower := strings.ToLower(packageID)
	if strings.HasPrefix(idLower, "system.") ||
		strings.HasPrefix(idLower, "microsoft.") ||
		strings.HasPrefix(idLower, "netstandard") ||
		strings.HasPrefix(idLower, "mscorlib") ||
		strings.HasPrefix(idLower, "windowsbase") ||
		strings.HasPrefix(idLower, "presentationcore") ||
		strings.HasPrefix(idLower, "presentationframework") {
		return true
	}
	return false
}

// ----------------------------------------------------------------------------
// LICENSE / DEPENDENCY LOOKUP
// ----------------------------------------------------------------------------

// getPackageInfo queries NuGet's registration API for a package ID/version.
// If version is empty, we pick the latest version.
func getPackageInfo(packageID, version string) (licenseExpr, licenseURL string, depGroups []DependencyGroup, err error) {
	url := fmt.Sprintf("https://api.nuget.org/v3/registration5-semver1/%s/index.json", strings.ToLower(packageID))
	resp, err := http.Get(url)
	if err != nil {
		return "", "", nil, fmt.Errorf("failed to get package info: %w", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != 200 {
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
			return "", "", nil, fmt.Errorf("no items in the last page for package %s", packageID)
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

// parseVersionFromRange extracts a version from something like "[1.2.3, )" -> "1.2.3"
func parseVersionFromRange(rangeStr string) string {
	if rangeStr == "" {
		return ""
	}
	if rangeStr[0] == '[' || rangeStr[0] == '(' {
		end := strings.IndexAny(rangeStr, ",)]")
		if end > 1 {
			return rangeStr[1:end]
		}
	}
	return rangeStr
}

// ----------------------------------------------------------------------------
// COPyleft DETECTION
// ----------------------------------------------------------------------------

func isCopyleft(license string) bool {
	copyleftLicenses := []string{"GPL-2.0", "GPL-3.0", "LGPL-2.1", "LGPL-3.0", "AGPL-3.0"}
	upper := strings.ToUpper(license)
	for _, cl := range copyleftLicenses {
		if strings.Contains(upper, strings.ToUpper(cl)) {
			return true
		}
	}
	return false
}

// ----------------------------------------------------------------------------
// SCANNING LOGIC
// ----------------------------------------------------------------------------

// visitedMu protects visited, which is a map from "PackageID@NormalizedVersion" -> *PackageReport
func processPackage(
	pkgID, version string,
	visited map[string]*PackageReport,
	level int,
	topLevels []string,
	wg *sync.WaitGroup,
	visitedMu *sync.Mutex,
) *PackageReport {
	defer wg.Done()
	acquireSemaphore()
	defer releaseSemaphore()

	if skipFrameworkAssembly(pkgID) {
		fmt.Printf("Skipping framework assembly: %s\n", pkgID)
		return nil
	}

	normVersion := normalizeVersion(version)
	key := pkgID + "@" + normVersion

	visitedMu.Lock()
	if existing, found := visited[key]; found {
		// Merge top-levels
		for _, t := range topLevels {
			if !stringSliceContains(existing.IntroducedBy, t) {
				existing.IntroducedBy = append(existing.IntroducedBy, t)
			}
		}
		visitedMu.Unlock()
		fmt.Printf("Already processed %s@%s, merging top-levels.\n", pkgID, normVersion)
		return existing
	}
	// Not in visited => create a new report
	report := &PackageReport{
		PackageID:    pkgID,
		Version:      version,
		Level:        level,
		IntroducedBy: append([]string{}, topLevels...),
	}
	visited[key] = report
	visitedMu.Unlock()

	if report.Version == "" {
		report.Version = "unknown"
	}
	fmt.Printf("Processing package: %s@%s\n", pkgID, normVersion)

	licenseExpr, licenseURL, depGroups, err := getPackageInfo(pkgID, version)
	if err != nil {
		// We won't show debug info in the HTML, but we do print to console
		fmt.Printf("Error retrieving license info for %s@%s: %v\n", pkgID, version, err)
		return report
	}
	report.LicenseExpression = licenseExpr
	report.LicenseURL = licenseURL
	if isCopyleft(licenseExpr) {
		report.IsCopyleft = true
	}

	// Recurse into dependencies
	var childWg sync.WaitGroup
	var childMu sync.Mutex
	for _, group := range depGroups {
		for _, dep := range group.Dependencies {
			depVer := parseVersionFromRange(dep.Range)
			if depVer == "" {
				fmt.Printf("No version specified for %s, skipping.\n", dep.Id)
				continue
			}
			childWg.Add(1)
			go func(childID, childVer string) {
				defer childWg.Done()
				wg.Add(1) // We'll call wg.Done() in the child
				childRep := processPackage(childID, childVer, visited, level+1, topLevels, wg, visitedMu)
				if childRep != nil {
					childMu.Lock()
					report.Dependencies = append(report.Dependencies, childRep)
					childMu.Unlock()
				}
			}(dep.Id, depVer)
		}
	}
	childWg.Wait()

	return report
}

func stringSliceContains(slice []string, s string) bool {
	for _, item := range slice {
		if item == s {
			return true
		}
	}
	return false
}

// ----------------------------------------------------------------------------
// BFS FLATTENING + HTML REPORT
// ----------------------------------------------------------------------------

func flattenBFS(reports []*PackageReport) []*PackageReport {
	var result []*PackageReport
	queue := append([]*PackageReport{}, reports...)
	for len(queue) > 0 {
		current := queue[0]
		queue = queue[1:]
		result = append(result, current)
		queue = append(queue, current.Dependencies...)
	}
	return result
}

func getLicensePriority(rep *PackageReport) int {
	if rep.IsCopyleft {
		return 0 // red
	}
	if rep.LicenseExpression == "" {
		return 1 // orange
	}
	return 2 // green
}

// buildHTMLForOneFile creates BFS table + DFS tree for a single .csproj file.
func buildHTMLForOneFile(
	csprojPath string,
	reports []*PackageReport,
	summary *Summary,
) string {
	if len(reports) == 0 {
		// No dependencies at all
		return fmt.Sprintf("<h3>No dependencies found in %s</h3>", csprojPath)
	}

	// BFS flatten
	flat := flattenBFS(reports)
	// Sort by license priority
	sort.Slice(flat, func(i, j int) bool {
		return getLicensePriority(flat[i]) < getLicensePriority(flat[j])
	})

	// Update summary stats
	for _, rep := range flat {
		summary.TotalPackages++
		if rep.Level == 0 {
			summary.DirectPackages++
		} else {
			summary.TransitivePackages++
		}
		if rep.IsCopyleft {
			summary.CopyleftPackages++
		}
	}

	var sb strings.Builder

	// Heading for BFS table
	sb.WriteString(fmt.Sprintf("<h2>Dependency List for %s</h2>\n", csprojPath))
	sb.WriteString("<table>\n")
	sb.WriteString("<tr><th>Level</th><th>Package</th><th>Version</th><th>License</th><th>Info URL</th><th>Introduced By</th></tr>\n")
	for _, rep := range flat {
		cssClass := getCssClass(rep)
		sb.WriteString(fmt.Sprintf("<tr class=\"%s\">", cssClass))
		sb.WriteString(fmt.Sprintf("<td>%d</td>", rep.Level))
		sb.WriteString(fmt.Sprintf("<td>%s</td>", rep.PackageID))
		sb.WriteString(fmt.Sprintf("<td>%s</td>", rep.Version))

		sb.WriteString(fmt.Sprintf("<td>%s</td>", rep.LicenseExpression))
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
		sb.WriteString("</tr>\n")
	}
	sb.WriteString("</table>\n")

	// DFS tree
	sb.WriteString(fmt.Sprintf("<h2>Dependency Tree for %s</h2>\n", csprojPath))
	sb.WriteString("<ul>\n")
	for _, top := range reports {
		sb.WriteString(toHTMLDFS(top))
	}
	sb.WriteString("</ul>\n")

	return sb.String()
}

// toHTMLDFS produces a nested <ul>/<li> DFS tree for a single PackageReport.
func toHTMLDFS(r *PackageReport) string {
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
	if len(r.Dependencies) > 0 {
		sb.WriteString("<ul>")
		for _, child := range r.Dependencies {
			sb.WriteString(toHTMLDFS(child))
		}
		sb.WriteString("</ul>")
	}
	sb.WriteString("</li>\n")
	return sb.String()
}

// ----------------------------------------------------------------------------
// MAIN
// ----------------------------------------------------------------------------

func main() {
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

	// We'll produce one BFS/DFS section per file,
	// but a single summary across all files.
	var sb strings.Builder

	// HTML header + CSS
	sb.WriteString("<html><head><title>Copyleft Scan Report</title>\n<style>\n")
	sb.WriteString("body { font-family: Arial, sans-serif; }\n")
	// Entire row coloring:
	sb.WriteString("tr.copyleft { background-color: red; color: white; }\n")
	sb.WriteString("tr.unknown { background-color: orange; color: black; }\n")
	sb.WriteString("tr.non-copyleft { background-color: green; color: black; }\n")
	// For the DFS tree:
	sb.WriteString("li.copyleft { background-color: red; color: white; padding: 5px; margin: 3px; }\n")
	sb.WriteString("li.unknown { background-color: orange; color: black; padding: 5px; margin: 3px; }\n")
	sb.WriteString("li.non-copyleft { background-color: green; color: black; padding: 5px; margin: 3px; }\n")

	sb.WriteString("table, th, td { border: 1px solid #ccc; border-collapse: collapse; padding: 5px; }\n")
	sb.WriteString("th { background-color: #f0f0f0; }\n")
	sb.WriteString("ul { list-style-type: none; }\n")
	sb.WriteString("</style></head><body>\n")

	sb.WriteString("<h1>Copyleft Scan Report</h1>\n")

	// We'll accumulate summary stats across all files.
	totalSummary := Summary{}

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

		// We'll track visited packages for this file separately
		visited := make(map[string]*PackageReport)
		var visitedMu sync.Mutex
		var wg sync.WaitGroup
		var topLevelReports []*PackageReport

		// For each direct <PackageReference>, we treat it as a top-level dep
		for _, group := range proj.ItemGroups {
			for _, pkg := range group.PackageReferences {
				wg.Add(1)
				go func(pr PackageReference) {
					rep := processPackage(pr.Include, pr.Version, visited, 0, []string{pr.Include}, &wg, &visitedMu)
					if rep != nil {
						// It's a top-level report
						topLevelReports = append(topLevelReports, rep)
					}
				}(pkg)
			}
		}
		wg.Wait()

		// Build BFS/DFS HTML for this file
		fileHTML := buildHTMLForOneFile(file, topLevelReports, &totalSummary)
		sb.WriteString(fileHTML)
	}

	// Now produce the combined summary across all files.
	sb.WriteString("<hr/>\n")
	sb.WriteString("<h2>Combined Summary</h2>\n")
	sb.WriteString("<ul>\n")
	sb.WriteString(fmt.Sprintf("<li>Total Packages Scanned: %d</li>\n", totalSummary.TotalPackages))
	sb.WriteString(fmt.Sprintf("<li>Direct Packages: %d</li>\n", totalSummary.DirectPackages))
	sb.WriteString(fmt.Sprintf("<li>Transitive Packages: %d</li>\n", totalSummary.TransitivePackages))
	sb.WriteString(fmt.Sprintf("<li>Copyleft Packages: %d</li>\n", totalSummary.CopyleftPackages))
	// We no longer track "ErrorCount" because we're not displaying debug info
	// or partial errors in the final HTML. If you want to track errors,
	// you could store them in the code, but the user asked for no debug info.
	sb.WriteString("</ul>\n")

	sb.WriteString("</body></html>\n")

	if err := ioutil.WriteFile(outHTML, []byte(sb.String()), 0644); err != nil {
		log.Fatalf("Failed to write HTML report: %v", err)
	}
	fmt.Printf("HTML report generated: %s\n", outHTML)
}
