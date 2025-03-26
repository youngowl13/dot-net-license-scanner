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

// ----------------------------
// Data Types
// ----------------------------

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
	Dependencies      []*PackageReport // Transitive dependencies
	Level             int              // 0 = direct dependency, >0 = transitive
	IntroducedBy      []string         // Direct dependency names that introduced this package
}

// Summary holds combined statistics.
type Summary struct {
	TotalPackages      int
	DirectPackages     int
	TransitivePackages int
	CopyleftPackages   int
}

// ----------------------------
// Concurrency Control (Limit to 20)
// ----------------------------
var concurrencySem = make(chan struct{}, 20)

func acquireSemaphore() {
	concurrencySem <- struct{}{}
}

func releaseSemaphore() {
	<-concurrencySem
}

// ----------------------------
// Version Normalization
// ----------------------------

// normalizeVersion removes trailing ".0" segments (e.g., "4.0.0.0" becomes "4.0.0").
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

// ----------------------------
// Skip Known .NET Framework Assemblies
// ----------------------------

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

// ----------------------------
// Helper Functions
// ----------------------------

// getCssClass returns the CSS class for a package report.
func getCssClass(rep *PackageReport) string {
	if rep.IsCopyleft {
		return "copyleft"
	}
	if rep.LicenseExpression == "" {
		return "unknown"
	}
	return "non-copyleft"
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

// parseVersionFromRange extracts a version from a dependency range string.
// For example, "[1.2.3, )" returns "1.2.3".
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

// getPackageInfo queries NuGet's registration API for a given package ID and version.
// If version is empty, it picks the latest available version.
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

// isCopyleft returns true if the given license string indicates a copyleft license.
// This function checks several common full-form and abbreviated identifiers.
func isCopyleft(license string) bool {
	lower := strings.ToLower(license)
	candidates := []string{
		"gpl-2.0", "gpl 2.0", "gnu general public license v2", "gnu gpl v2",
		"gpl-3.0", "gpl 3.0", "gnu general public license v3", "gnu gpl v3",
		"lgpl-2.1", "lgpl 2.1", "gnu lesser general public license v2.1", "gnu lgpl v2.1",
		"lgpl-3.0", "lgpl 3.0", "gnu lesser general public license v3", "gnu lgpl v3",
		"agpl-3.0", "agpl 3.0", "gnu affero general public license",
	}
	for _, candidate := range candidates {
		if strings.Contains(lower, candidate) {
			return true
		}
	}
	return false
}

// ----------------------------
// Scanning Logic
// ----------------------------

// processPackage recursively processes a package and its dependencies.
// topLevels is a slice of direct dependency names (the Include values) that introduced this package.
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

	if level == 0 && len(topLevels) == 0 {
		topLevels = []string{pkgID}
	}

	visitedMu.Lock()
	if existing, found := visited[key]; found {
		for _, t := range topLevels {
			if !containsString(existing.IntroducedBy, t) {
				existing.IntroducedBy = append(existing.IntroducedBy, t)
			}
		}
		visitedMu.Unlock()
		fmt.Printf("Already processed %s@%s, merging top-levels.\n", pkgID, normVersion)
		return existing
	}
	visitedMu.Unlock()

	displayVersion := version
	if displayVersion == "" {
		displayVersion = "unknown"
	}
	report := &PackageReport{
		PackageID:    pkgID,
		Version:      displayVersion,
		Level:        level,
		IntroducedBy: append([]string{}, topLevels...),
	}
	visitedMu.Lock()
	visited[key] = report
	visitedMu.Unlock()

	fmt.Printf("Processing package: %s@%s\n", pkgID, normVersion)
	licenseExpr, licenseURL, depGroups, err := getPackageInfo(pkgID, version)
	if err != nil {
		fmt.Printf("Error retrieving license info for %s@%s: %v\n", pkgID, version, err)
		return report
	}
	report.LicenseExpression = licenseExpr
	report.LicenseURL = licenseURL
	if isCopyleft(licenseExpr) {
		report.IsCopyleft = true
	}

	var childWg sync.WaitGroup
	var childMu sync.Mutex
	for _, group := range depGroups {
		for _, dep := range group.Dependencies {
			depVer := parseVersionFromRange(dep.Range)
			if depVer == "" {
				fmt.Printf("No version specified for dependency %s, skipping.\n", dep.Id)
				continue
			}
			childWg.Add(1)
			go func(childID, childVer string) {
				defer childWg.Done()
				wg.Add(1)
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

// flattenBFS returns a slice of PackageReports in breadth-first order.
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

// ----------------------------
// HTML Report Generation
// ----------------------------

// toHTMLDFS produces a nested DFS tree as HTML for a single PackageReport (without debug info).
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

// buildHTMLForOneFile builds the HTML for one csproj file.
func buildHTMLForOneFile(
	csprojPath string,
	reports []*PackageReport,
	summary *Summary,
) string {
	var sb strings.Builder
	sb.WriteString(fmt.Sprintf("<h2>Dependency List for %s</h2>\n", csprojPath))
	flat := flattenBFS(reports)
	sort.Slice(flat, func(i, j int) bool {
		pi, pj := 2, 2
		if flat[i].IsCopyleft {
			pi = 0
		} else if flat[i].LicenseExpression == "" {
			pi = 1
		}
		if flat[j].IsCopyleft {
			pj = 0
		} else if flat[j].LicenseExpression == "" {
			pj = 1
		}
		return pi < pj
	})
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

	sb.WriteString(fmt.Sprintf("<h2>Dependency Tree for %s</h2>\n", csprojPath))
	sb.WriteString("<ul>\n")
	for _, rep := range reports {
		sb.WriteString(toHTMLDFS(rep))
	}
	sb.WriteString("</ul>\n")

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
	return sb.String()
}

// generateHTMLReport creates the final HTML report for all csproj files.
func generateHTMLReport(allReports map[string][]*PackageReport, summary *Summary) string {
	var sb strings.Builder
	sb.WriteString("<html><head><title>Copyleft Scan Report</title>\n<style>\n")
	sb.WriteString("body { font-family: Arial, sans-serif; }\n")
	sb.WriteString("tr.copyleft { background-color: red; }\n")
	sb.WriteString("tr.unknown { background-color: orange; }\n")
	sb.WriteString("tr.non-copyleft { background-color: green; }\n")
	sb.WriteString("li.copyleft { background-color: red; padding: 5px; margin: 3px; }\n")
	sb.WriteString("li.unknown { background-color: orange; padding: 5px; margin: 3px; }\n")
	sb.WriteString("li.non-copyleft { background-color: green; padding: 5px; margin: 3px; }\n")
	sb.WriteString("table, th, td { border: 1px solid #ccc; border-collapse: collapse; padding: 5px; }\n")
	sb.WriteString("th { background-color: #f0f0f0; }\n")
	sb.WriteString("ul { list-style-type: none; }\n")
	sb.WriteString("</style></head><body>\n")
	sb.WriteString("<h1>Copyleft Scan Report</h1>\n")
	sb.WriteString("<h2>Combined Summary</h2>\n<ul>\n")
	sb.WriteString(fmt.Sprintf("<li>Total Packages Scanned: %d</li>\n", summary.TotalPackages))
	sb.WriteString(fmt.Sprintf("<li>Direct Packages: %d</li>\n", summary.DirectPackages))
	sb.WriteString(fmt.Sprintf("<li>Transitive Packages: %d</li>\n", summary.TransitivePackages))
	sb.WriteString(fmt.Sprintf("<li>Copyleft Packages: %d</li>\n", summary.CopyleftPackages))
	sb.WriteString("</ul>\n")
	for path, reports := range allReports {
		sb.WriteString(buildHTMLForOneFile(path, reports, summary))
	}
	sb.WriteString("</body></html>\n")
	return sb.String()
}

// ----------------------------
// File Search
// ----------------------------

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

// ----------------------------
// Main
// ----------------------------

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

	allReports := make(map[string][]*PackageReport)
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

		visited := make(map[string]*PackageReport)
		var visitedMu sync.Mutex
		var wg sync.WaitGroup
		var reports []*PackageReport

		// For each direct dependency, use its Include as the top-level identifier.
		for _, group := range proj.ItemGroups {
			for _, pkg := range group.PackageReferences {
				wg.Add(1)
				go func(pr PackageReference) {
					rep := processPackage(pr.Include, pr.Version, visited, 0, []string{pr.Include}, &wg, &visitedMu)
					if rep != nil {
						reports = append(reports, rep)
					}
				}(pkg)
			}
		}
		wg.Wait()
		allReports[file] = reports
	}

	htmlReport := generateHTMLReport(allReports, &totalSummary)
	if err := ioutil.WriteFile(outHTML, []byte(htmlReport), 0644); err != nil {
		log.Fatalf("Failed to write HTML report: %v", err)
	}
	fmt.Printf("HTML report generated: %s\n", outHTML)
}
