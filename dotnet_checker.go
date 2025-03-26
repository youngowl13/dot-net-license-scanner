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

// ---------------------------------
// Data Structures
// ---------------------------------

type PackageReference struct {
	XMLName xml.Name `xml:"PackageReference"`
	Include string   `xml:"Include,attr"` // e.g. "AutoMapper"
	Version string   `xml:"Version,attr"` // e.g. "12.0.1"
}

type Project struct {
	XMLName    xml.Name `xml:"Project"`
	ItemGroups []struct {
		PackageReferences []PackageReference `xml:"PackageReference"`
	} `xml:"ItemGroup"`
}

// NuGet metadata
type Dependency struct {
	Id    string `json:"id"`
	Range string `json:"range"`
}

type DependencyGroup struct {
	TargetFramework string       `json:"targetFramework"`
	Dependencies    []Dependency `json:"dependencies"`
}

type CatalogEntry struct {
	Version           string            `json:"version"`
	LicenseExpression string            `json:"licenseExpression"`
	LicenseURL        string            `json:"licenseUrl"`
	DependencyGroups  []DependencyGroup `json:"dependencyGroups"`
}

type NuGetRegistration struct {
	Items []struct {
		Items []struct {
			CatalogEntry CatalogEntry `json:"catalogEntry"`
		} `json:"items"`
	} `json:"items"`
}

// Final report data
type PackageReport struct {
	PackageID         string
	Version           string // e.g. "12.0.1" or "version not known"
	LicenseExpression string // e.g. "MIT" or empty
	LicenseURL        string
	IsCopyleft        bool
	Dependencies      []*PackageReport
	Level             int      // 0=direct, >0=transitive
	IntroducedBy      []string // direct dependencies that introduced this package
}

type Summary struct {
	TotalPackages      int
	DirectPackages     int
	TransitivePackages int
	CopyleftPackages   int
}

// ---------------------------------
// Concurrency Limit (20)
// ---------------------------------

var concurrencySem = make(chan struct{}, 20)

func acquireSemaphore() {
	concurrencySem <- struct{}{}
}

func releaseSemaphore() {
	<-concurrencySem
}

// ---------------------------------
// Helper: skip .NET framework assemblies
// ---------------------------------

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

// ---------------------------------
// Helper: normalize version
// ---------------------------------

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

// ---------------------------------
// Helper: string slice
// ---------------------------------

func containsString(slice []string, s string) bool {
	for _, item := range slice {
		if item == s {
			return true
		}
	}
	return false
}

// ---------------------------------
// Helper: parseVersionFromRange
// ---------------------------------

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

// ---------------------------------
// License detection
// ---------------------------------

func isCopyleft(license string) bool {
	lower := strings.ToLower(license)
	candidates := []string{
		"gpl-2.0", "gpl 2.0", "gnu general public license v2", "gnu gpl v2",
		"gpl-3.0", "gpl 3.0", "gnu general public license v3", "gnu gpl v3",
		"lgpl-2.1", "lgpl 2.1", "gnu lesser general public license v2.1", "gnu lgpl v2.1",
		"lgpl-3.0", "lgpl 3.0", "gnu lesser general public license v3", "gnu lgpl v3",
		"agpl-3.0", "agpl 3.0", "gnu affero general public license",
	}
	for _, c := range candidates {
		if strings.Contains(lower, c) {
			return true
		}
	}
	return false
}

// ---------------------------------
// getPackageInfo: fetch license info from NuGet
// ---------------------------------

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

	// If no version specified, pick the latest version from the last page
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

	// Otherwise, find the specified version
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

// ---------------------------------
// BFS flatten
// ---------------------------------

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

// ---------------------------------
// getCssClass
// ---------------------------------

func getCssClass(rep *PackageReport) string {
	if rep.IsCopyleft {
		return "copyleft"
	}
	if rep.LicenseExpression == "" {
		return "unknown"
	}
	return "non-copyleft"
}

// ---------------------------------
// processPackage: main scanning logic
// ---------------------------------

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

	// Skip .NET assemblies
	if skipFrameworkAssembly(pkgID) {
		fmt.Printf("Skipping framework assembly: %s\n", pkgID)
		return nil
	}

	if level == 0 && len(topLevels) == 0 {
		topLevels = []string{pkgID}
	}

	normVersion := normalizeVersion(version)
	key := pkgID + "@" + normVersion

	// If we have already processed it, merge top-levels
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

	// If .csproj omitted version, we display "version not known"
	displayVersion := version
	if displayVersion == "" {
		displayVersion = "version not known"
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

	// Recurse transitive dependencies
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

// ---------------------------------
// buildHTMLForOneFile
// ---------------------------------

func buildHTMLForOneFile(csprojPath string, reports []*PackageReport, summary *Summary) string {
	var sb strings.Builder
	sb.WriteString(fmt.Sprintf("<h2>Dependency List for %s</h2>\n", csprojPath))

	// BFS flatten
	flat := flattenBFS(reports)
	// Sort by license priority
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

	// BFS Table
	sb.WriteString("<table>\n")
	sb.WriteString("<tr><th>Level</th><th>Package</th><th>Version</th><th>License</th><th>Info URL</th><th>Introduced By</th></tr>\n")
	for _, rep := range flat {
		cssClass := getCssClass(rep)
		licenseToShow := rep.LicenseExpression
		if licenseToShow == "" {
			licenseToShow = "license not known"
		}
		sb.WriteString(fmt.Sprintf("<tr class=\"%s\">", cssClass))
		sb.WriteString(fmt.Sprintf("<td>%d</td>", rep.Level))
		sb.WriteString(fmt.Sprintf("<td>%s</td>", rep.PackageID))
		sb.WriteString(fmt.Sprintf("<td>%s</td>", rep.Version))
		sb.WriteString(fmt.Sprintf("<td>%s</td>", licenseToShow))

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

	// DFS Tree
	sb.WriteString(fmt.Sprintf("<h2>Dependency Tree for %s</h2>\n", csprojPath))
	sb.WriteString("<ul>\n")
	for _, rep := range reports {
		sb.WriteString(toHTMLDFS(rep))
	}
	sb.WriteString("</ul>\n")

	// Update summary
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

// ---------------------------------
// generateHTMLReport
// ---------------------------------

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

	// Combined Summary (will be updated by each file)
	sb.WriteString("<h2>Combined Summary</h2>\n")
	sb.WriteString("<ul>\n")
	sb.WriteString(fmt.Sprintf("<li>Total Packages Scanned: %d</li>\n", summary.TotalPackages))
	sb.WriteString(fmt.Sprintf("<li>Direct Packages: %d</li>\n", summary.DirectPackages))
	sb.WriteString(fmt.Sprintf("<li>Transitive Packages: %d</li>\n", summary.TransitivePackages))
	sb.WriteString(fmt.Sprintf("<li>Copyleft Packages: %d</li>\n", summary.CopyleftPackages))
	sb.WriteString("</ul>\n")

	// For each .csproj file
	for path, reports := range allReports {
		sb.WriteString(buildHTMLForOneFile(path, reports, summary))
	}

	sb.WriteString("</body></html>\n")
	return sb.String()
}

// ---------------------------------
// findCsprojFiles
// ---------------------------------

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

// ---------------------------------
// main
// ---------------------------------

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

		// For each direct dependency, spawn a goroutine
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

	// Build final HTML
	htmlReport := generateHTMLReport(allReports, &totalSummary)
	if err := ioutil.WriteFile(outHTML, []byte(htmlReport), 0644); err != nil {
		log.Fatalf("Failed to write HTML report: %v", err)
	}
	fmt.Printf("HTML report generated: %s\n", outHTML)
}
