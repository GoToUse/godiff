//	File/Directory diff tool with HTML output
//	Copyright (C) 2012   Siu Pin Chao
//
//	This program is free software: you can redistribute it and/or modify
//	it under the terms of the GNU General Public License as published by
//	the Free Software Foundation, either version 3 of the License, or
//	(at your option) any later version.
//
//	This program is distributed in the hope that it will be useful,
//	but WITHOUT ANY WARRANTY; without even the implied warranty of
//	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//	GNU General Public License for more details.
//
//	You should have received a copy of the GNU General Public License
//	along with this program.  If not, see <http://www.gnu.org/licenses/>.
//
// Description:
//
//	This program can be use to compare files and directories for differences.
//	When comparing directories, it iterates through all files in both directories
//	and compare files having the same name.
//
//	It uses the algorithm from "An O(ND) Difference Algorithm and its Variations"
//	by Eugene Myers Algorithmic Vol. 1 No. 2, 1986, p 251.
//
// Main Features:
//   - Supports UTF8 file.
//   - Show differences within a line
//   - Options for ignore case, white spaces compare, blank lines etc.
//
// Main aim of the application is to try out the features in the go programming language. (golang.org)
//
//   - Slices: Used extensively, and re-slicing too whenever it make sense.
//
//   - File I/O: Use Mmap for reading text files
//
//   - Function Closure: Use in callbacks functions to handle both file and line compare
//
//   - Goroutines: for running multiple file compares concurrently, using channels and mutex too.
//
//     History
//     -------
//     2012/09/20  Created
package main

import (
	"bufio"
	"bytes"
	"compress/bzip2"
	"compress/gzip"
	"flag"
	"fmt"
	"hash/crc32"
	"html"

	"io"
	"os"
	"regexp"
	"runtime"
	"runtime/pprof"
	"sort"
	"strings"
	"sync"
	"time"
	"unicode"
	"unicode/utf8"
)

const (
	// VERSION Version number
	VERSION = "0.0.2"

	// BinaryCheckSize Scan at up to this size in file for '\0' in test for binary file
	BinaryCheckSize = 65536

	// OutputBufSize Output buffer size
	OutputBufSize = 65536

	// ContextLines default number of context lines to display
	ContextLines = 3

	// PathSeparator convenient shortcut
	PathSeparator = string(os.PathSeparator)

	// MmapThreshold use mmap for file greater than this size, for smaller files just use Read() instead.
	MmapThreshold = 8 * 1024

	// NumPreviewLines Number of lines to print for previewing file
	NumPreviewLines = 10
)

// Error Messages
const (
	MsgFileSizeZero   = "File has size 0"
	MsgFileNotExists  = "File does not exist"
	MsgDirNotExists   = "Directory does not exist"
	MsgFileIsBinary   = "This is a binary file"
	MsgFileDiffers    = "File differs"
	MsgBinFileDiffers = "File differs. This is a binary file"
	MsgFileIdentical  = "Files are the same"
	MsgFileTooBig     = "File too big"
	MsgThisIsDir      = "This is a directory"
	MsgThisIsFile     = "This is a file"
)

// FileData file data
type FileData struct {
	name     string
	info     os.FileInfo
	osFile   *os.File
	errorMsg string
	isBinary bool
	isMapped bool
	data     []byte
}

// OutputFormat Output to diff as html or text format
type OutputFormat struct {
	buf1, buf2           bytes.Buffer
	name1, name2         string
	fileInfo1, fileInfo2 os.FileInfo
	headerPrinted        bool
	linenoWidth          int
}

const (
	DiffOpSame   = 1
	DiffOpModify = 2
	DiffOpInsert = 3
	DiffOpRemove = 4
)

type DiffOp struct {
	op           int
	start1, end1 int
	start2, end2 int
}

// DiffChanger Interface for report_diff() callbacks.
type DiffChanger interface {
	diffLines([]DiffOp)
}

// DiffChangerData Data use by DiffChanger
type DiffChangerData struct {
	*OutputFormat
	file1, file2 [][]byte
}

// DiffChangerText changes to be output in Text format
type DiffChangerText struct {
	DiffChangerData
}

// DiffChangerUnifiedText changes to be output in Unified Text format
type DiffChangerUnifiedText struct {
	DiffChangerData
}

// DiffChangerHtml changes to be output in Html format
type DiffChangerHtml struct {
	DiffChangerData
}

// DiffChangerUnifiedHtml changes to be output in Unified Html format
type DiffChangerUnifiedHtml struct {
	DiffChangerData
}

const HtmlHeader = `<!doctype html><html><head>
<meta http-equiv="content-type" content="text/html;charset=utf-8">`

const HtmlCss = `<style type="text/css">
.tab {border-color:#808080; border-style:solid; border-width:1px 1px 1px 1px; border-collapse:collapse;}
.tth {border-color:#808080; border-style:solid; border-width:1px 1px 1px 1px; border-collapse:collapse; padding:4px; vertical-align:top; text-align:left; background-color:#E0E0E0;}
.ttd {border-color:#808080; border-style:solid; border-width:1px 1px 1px 1px; border-collapse:collapse; padding:4px; vertical-align:top; text-align:left;}
.hdr {color:black; font-size:85%;}
.inf {color:#C08000; font-size:85%;}
.err {color:red; font-size:85%; font-weight:bold; margin:0;}
.msg {color:#508050; font-size:85%; font-weight:bold; margin:0;}
.lno {color:#C08000; background-color:white; font-style:italic; margin:0;}
.nop {color:black; font-size:75%; font-family:monospace; white-space:pre; margin:0; display:block;}
.upd {color:black; font-size:75%; font-family:monospace; white-space:pre; margin:0; background-color:#CFCFFF; display:block;}
.emp {color:black; font-size:75%; font-family:monospace; white-space:pre; margin:0; background-color:#E0E0E0; display:block;}
.add {color:black; font-size:75%; font-family:monospace; white-space:pre; margin:0; background-color:#CFFFCF; display:block;}
.del {color:black; font-size:75%; font-family:monospace; white-space:pre; margin:0; background-color:#FFCFCF; display:block;}
.chg {color:#C00080; background-color:#AFAFDF;}
</style>`

const HtmlLegend = `<br><b>Legend:</b><br><table class="tab">
<tr><td class="tth"><span class="hdr">filename 1</span></td><td class="tth"><span class="hdr">filename 2</span></td></tr>
<tr><td class="ttd">
<span class="del"><span class="lno">1 </span>line deleted</span>
<span class="nop"><span class="lno">2 </span>no change</span>
<span class="upd"><span class="lno">3 </span>line modified</span>
</td>
<td class="ttd">
<span class="add"><span class="lno">1 </span>line added</span>
<span class="nop"><span class="lno">2 </span>no change</span>
<span class="upd"><span class="lno">3 </span><span class="chg">L</span>ine <span class="chg">M</span>modified</span>
</td></tr>
</table>
`

// command line arguments
var (
	flagPprofFile            string
	flagVersion              bool = false
	flagCmpIgnoreCase        bool = false
	flagCmpIgnoreBlankLines  bool = false
	flagCmpIgnoreSpaceChange bool = false
	flagCmpIgnoreAllSpace    bool = false
	flagUnicodeCaseAndSpace  bool = false
	flagShowIdenticalFiles   bool = false
	flagSuppressLineChanges  bool = false
	flagSuppressMissingFile  bool = false
	flagOutputAsText         bool = false
	flagUnifiedContext       bool = false
	flagContextLines         int  = ContextLines
	flagExcludeFiles         string
	flagMaxGoroutines        = 1
)

// JobQueue for goroutines
type JobQueue struct {
	name1, name2 string
	info1, info2 os.FileInfo
}

// Queue queue for goroutines diffFile
var (
	jobQueue chan JobQueue
	jobWait  sync.WaitGroup
)

// Files/Dirs to excludes
var regexpExcludeFiles *regexp.Regexp

// Buffered stdout
var (
	out     = bufio.NewWriterSize(os.Stdout, OutputBufSize)
	outLock sync.Mutex
)

// html entity strings
var (
	htmlEntityAmp    = html.EscapeString("&")
	htmlEntityGt     = html.EscapeString(">")
	htmlEntityLt     = html.EscapeString("<")
	htmlEntityQuote  = html.EscapeString("'")
	htmlEntityDQuote = html.EscapeString("\"")
)

// functions to compare line and computer hash values,
// these will be setup based on flags: -b -w -U etc.
var (
	compareLine func([]byte, []byte) bool
	computeHash func([]byte) uint32
)

var blankLine = make([]byte, 0)

func version() {
	fmt.Printf("godiff. Version %s\n", VERSION)
	fmt.Printf("Copyright (C) 2012 Siu Pin Chao.\n")
}

func usage(msg string) {
	if msg != "" {
		fmt.Fprintf(os.Stderr, "%s\n", msg)
	}
	fmt.Fprint(os.Stderr, "A text file comparison tool displaying differences in HTML\n\n")
	fmt.Fprint(os.Stderr, "usage: godiff <options> <file|dir> <file|dir>\n")
	fmt.Fprint(os.Stderr, "\n<options>\n")
	flag.PrintDefaults()
	os.Exit(2)
}

func usage0() {
	usage("")
}

// Main routine.
func main() {

	// setup command line options
	flag.Usage = usage0
	flag.StringVar(&flagPprofFile, "prof", "", "Write pprof output to file")
	flag.StringVar(&flagExcludeFiles, "X", "", "Exclude files/directories matching this regexp pattern")
	flag.BoolVar(&flagVersion, "v", flagVersion, "Print version information")
	flag.IntVar(&flagContextLines, "c", flagContextLines, "Include N lines of context before and after changes")
	flag.IntVar(&flagMaxGoroutines, "g", flagMaxGoroutines, "Max number of goroutines to use for file comparison")
	flag.BoolVar(&flagCmpIgnoreSpaceChange, "b", flagCmpIgnoreSpaceChange, "Ignore changes in the amount of white space")
	flag.BoolVar(&flagCmpIgnoreAllSpace, "w", flagCmpIgnoreAllSpace, "Ignore all white space")
	flag.BoolVar(&flagCmpIgnoreCase, "i", flagCmpIgnoreCase, "Ignore case differences in file contents")
	flag.BoolVar(&flagCmpIgnoreBlankLines, "B", flagCmpIgnoreBlankLines, "Ignore changes whose lines are all blank")
	flag.BoolVar(&flagUnicodeCaseAndSpace, "unicode", flagUnicodeCaseAndSpace, "Apply unicode rules for white space and upper/lower case")
	flag.BoolVar(&flagShowIdenticalFiles, "s", flagShowIdenticalFiles, "Report when two files are the identical")
	flag.BoolVar(&flagSuppressLineChanges, "l", flagSuppressLineChanges, "Do not display changes within lines")
	flag.BoolVar(&flagSuppressMissingFile, "m", flagSuppressMissingFile, "Do not show content if corresponding file is missing")
	flag.BoolVar(&flagUnifiedContext, "u", flagUnifiedContext, "Unified context")
	flag.BoolVar(&flagOutputAsText, "n", flagOutputAsText, "Output using 'diff' text format instead of HTML")
	flag.Parse()

	if flagVersion {
		version()
		os.Exit(0)
	}

	// write pprof info
	if flagPprofFile != "" {
		pf, err := os.Create(flagPprofFile)
		if err != nil {
			usage(err.Error())
		}
		pprof.StartCPUProfile(pf)
		defer pprof.StopCPUProfile()
	}

	if flagExcludeFiles != "" {
		r, err := regexp.Compile(flagExcludeFiles)
		if err != nil {
			usage("Invalid exclude regex: " + err.Error())
		}
		regexpExcludeFiles = r
	}

	// flush output on termination
	defer func() {
		out.Flush()
	}()

	// choose which compare and hash function to use
	if flagCmpIgnoreCase || flagCmpIgnoreSpaceChange || flagCmpIgnoreAllSpace {
		if flagUnicodeCaseAndSpace {
			computeHash = computeHashUnicode
			compareLine = compareLineUnicode
		} else {
			computeHash = computeHashBytes
			compareLine = compareLineBytes
		}
	} else {
		computeHash = computeHashExact
		compareLine = bytes.Equal
	}

	// get command line args
	args := flag.Args()
	if len(args) < 2 {
		usage("Missing files")
	}

	if len(args) > 2 {
		usage("Too many files")
	}

	// get the directory name or filename
	file1, file2 := args[0], args[1]

	// check file type
	finfo1, err1 := os.Stat(file1)
	finfo2, err2 := os.Stat(file2)

	// Unable to find either file/directory
	if err1 != nil || err2 != nil {
		if err1 != nil {
			fmt.Fprintf(os.Stderr, "%s\n", err1.Error())
		}
		if err2 != nil {
			fmt.Fprintf(os.Stderr, "%s\n", err2.Error())
		}
		os.Exit(1)
	}

	if finfo1.IsDir() != finfo2.IsDir() {
		usage("Unable to compare file and directory")
	}

	if !flagOutputAsText {
		out.WriteString(HtmlHeader)
		fmt.Fprintf(out, "<title>Compare %s vs %s</title>\n", html.EscapeString(file1), html.EscapeString(file2))
		out.WriteString(HtmlCss)
		out.WriteString("</head><body>\n")
		fmt.Fprintf(out, "<p>Compare <strong>%s</strong> vs <strong>%s</strong></p>\n", html.EscapeString(file1), html.EscapeString(file2))
	}

	switch {
	case !finfo1.IsDir() && !finfo2.IsDir():
		diffFile(file1, file2, finfo1, finfo2)

	case finfo1.IsDir() && finfo2.IsDir():
		jobQueueInit()
		diffDirs(file1, file2, finfo1, finfo2)
		jobQueueFinish()
	}

	if !flagOutputAsText {
		fmt.Fprintf(out, "Generated on %s<br>", time.Now().Format(time.RFC1123))
		out.WriteString(HtmlLegend)
		out.WriteString("</body></html>\n")
	}
}

// Call the diff algorithm.
func doDiff(data1, data2 []int) ([]bool, []bool) {
	len1, len2 := len(data1), len(data2)
	change1, change2 := make([]bool, len1), make([]bool, len2)

	size := (len1+len2+1)*2 + 2
	v := make([]int, size*2)

	// Run diff compare algorithm.
	algorithmLcs(data1, data2, change1, change2, v)

	return change1, change2
}

// Find the beginning/end of this 'changed' segment
func nextChangeSegment(start int, change []bool, data []int) (int, int, int) {

	// find the end of this changes segment
	end := start + 1
	for end < len(change) && change[end] {
		end++
	}

	// skip blank lines in the begining and end of the changes
	i, j := start, end
	for i < end && data[i] == 0 {
		i++
	}
	for j > i && data[j-1] == 0 {
		j--
	}

	return end, i, j
}

// Add segment to the group of changes. Add context lines before and after if necessary
func addChangeSegment(chg DiffChanger, ops []DiffOp, op DiffOp) []DiffOp {
	last1, last2 := 0, 0
	if len(ops) > 0 {
		lastOp := ops[len(ops)-1]
		last1, last2 = lastOp.end1, lastOp.end2
	}

	gap1, gap2 := op.start1-last1, op.start2-last2
	if len(ops) > 0 && (op.op == 0 || (gap1 > flagContextLines*2 && gap2 > flagContextLines*2)) {
		e1, e2 := minInt(op.start1, last1+flagContextLines), minInt(op.start2, last2+flagContextLines)
		if e1 > last1 || e2 > last2 {
			ops = append(ops, DiffOp{DiffOpSame, last1, e1, last2, e2})
		}
		chg.diffLines(ops)
		ops = ops[:0]
	}

	c1, c2 := maxInt(last1, op.start1-flagContextLines), maxInt(last2, op.start2-flagContextLines)
	if c1 < op.start1 || c2 < op.start2 {
		ops = append(ops, DiffOp{DiffOpSame, c1, op.start1, c2, op.start2})
	}

	if op.op != 0 {
		ops = append(ops, op)
	}
	return ops
}

// Report diff changes.
// For each group of change, call the diff_lines() function
func reportDiff(chg DiffChanger, data1, data2 []int, change1, change2 []bool) bool {
	len1, len2 := len(change1), len(change2)
	i1, i2 := 0, 0
	ops := make([]DiffOp, 0, 16)
	changed := false
	var m1start, m1end, m2start, m2end int

	// scan for changes
	for i1 < len1 || i2 < len2 {
		switch {
		// no change, advance both i1 and i2 to next set of changes
		case i1 < len1 && i2 < len2 && !change1[i1] && !change2[i2]:
			i1++
			i2++

		// change in both lists
		case i1 < len1 && i2 < len2 && change1[i1] && change2[i2]:
			i1, m1start, m1end = nextChangeSegment(i1, change1, data1)
			i2, m2start, m2end = nextChangeSegment(i2, change2, data2)

			opMode := 0
			switch {
			case m1start < m1end && m2start < m2end:
				opMode = DiffOpModify
			case m1start < m1end:
				opMode = DiffOpRemove
			case m2start < m2end:
				opMode = DiffOpInsert
			}
			if opMode != 0 {
				ops = addChangeSegment(chg, ops, DiffOp{opMode, m1start, m1end, m2start, m2end})
				changed = true
			}

		case i1 < len1 && change1[i1]:
			i1, m1start, m1end = nextChangeSegment(i1, change1, data1)
			if m1start < m1end {
				ops = addChangeSegment(chg, ops, DiffOp{DiffOpRemove, m1start, m1end, i2, i2})
				changed = true
			}

		case i2 < len2 && change2[i2]:
			i2, m2start, m2end = nextChangeSegment(i2, change2, data2)
			if m2start < m2end {
				ops = addChangeSegment(chg, ops, DiffOp{DiffOpInsert, i1, i1, m2start, m2end})
				changed = true
			}

		default: // should not reach here
			return true
		}
	}
	if len(ops) > 0 {
		addChangeSegment(chg, ops, DiffOp{0, len1, len1, len2, len2})
	}
	return changed
}

// convert byte to lower case
func toLowerByte(b byte) byte {
	if b >= 'A' && b <= 'Z' {
		return b - 'A' + 'a'
	}
	return b
}

// split text into array of individual rune position, and another array for comparison.
func splitRunes(s []byte) ([]int, []int) {

	pos := make([]int, len(s)+1)
	cmp := make([]int, len(s))

	var h, i, n int

	for i < len(s) {
		pos[n] = i
		b := s[i]
		if b < utf8.RuneSelf {
			if flagCmpIgnoreCase {
				if flagUnicodeCaseAndSpace {
					h = int(unicode.ToLower(rune(b)))
				} else {
					h = int(toLowerByte(b))
				}
			} else {
				h = int(b)
			}
			i++
		} else {
			r, rSize := utf8.DecodeRune(s[i:])
			if flagCmpIgnoreCase && flagUnicodeCaseAndSpace {
				h = int(unicode.ToLower(r))
			} else {
				h = int(r)
			}
			i += rSize
		}
		cmp[n] = h
		n = n + 1
	}
	pos[n] = i
	return pos[:n+1], cmp[:n]
}

// Write bytes to buffer, ready to be output as html,
// replace special chars with html-entities
func writeHtmlBytes(buf *bytes.Buffer, line []byte) {
	var esc string
	lastI := 0
	for i, v := range line {
		switch v {
		case '<':
			esc = htmlEntityLt
		case '>':
			esc = htmlEntityGt
		case '&':
			esc = htmlEntityAmp
		case '\'':
			esc = htmlEntityQuote
		case '"':
			esc = htmlEntityDQuote
		default:
			continue
		}
		buf.Write(line[lastI:i])
		buf.WriteString(esc)
		lastI = i + 1
	}
	buf.Write(line[lastI:])
}

func htmlPreviewFile(buf *bytes.Buffer, lines [][]byte) {
	n := minInt(NumPreviewLines, len(lines))
	w := len(fmt.Sprintf("%d", n))
	buf.WriteString("<span class=\"nop\">")
	for lineno, line := range lines[0:n] {
		writeHtmlLineno(buf, lineno+1, w)
		writeHtmlBytes(buf, line)
		buf.WriteByte('\n')
	}
	buf.WriteString("</span></span>")
}

func outputDiffMessageContent(filename1, filename2 string, info1, info2 os.FileInfo, msg1, msg2 string, data1, data2 [][]byte, isError bool) {

	if flagOutputAsText {
		outAcquireLock()
		if flagUnifiedContext {
			fmt.Fprintf(out, "<<< %s: %s\n", filename1, msg1)
			fmt.Fprintf(out, ">>> %s: %s\n\n", filename2, msg2)
		} else {
			fmt.Fprintf(out, "--- %s: %s\n", filename1, msg1)
			fmt.Fprintf(out, "+++ %s: %s\n\n", filename2, msg2)
		}
		outReleaseLock()
	} else {

		outfmt := OutputFormat{
			name1:     filename1,
			name2:     filename2,
			fileInfo1: info1,
			fileInfo2: info2,
		}

		var span string
		if isError {
			span = "<span class=\"err\">"
		} else {
			span = "<span class=\"msg\">"
		}

		if msg1 != "" {
			outfmt.buf1.WriteString(span)
			writeHtmlBytes(&outfmt.buf1, []byte(msg1))
			outfmt.buf1.WriteString("</span><br>")
		} else if len(data1) > 0 {
			htmlPreviewFile(&outfmt.buf1, data1)
		}

		if msg2 != "" {
			outfmt.buf2.WriteString(span)
			writeHtmlBytes(&outfmt.buf2, []byte(msg2))
			outfmt.buf2.WriteString("</span><br>")
		} else if len(data2) > 0 {
			htmlPreviewFile(&outfmt.buf2, data2)
		}

		htmlFileTable(&outfmt)

		out.WriteString("<tr><td class=\"ttd\">")
		out.Write(outfmt.buf1.Bytes())

		out.WriteString("</td><td class=\"ttd\">")
		out.Write(outfmt.buf2.Bytes())

		out.WriteString("</td></tr>\n")
		out.WriteString("</table><br>\n")
		outReleaseLock()
	}
}

func outputDiffMessage(filename1, filename2 string, info1, info2 os.FileInfo, msg1, msg2 string, isError bool) {
	outputDiffMessageContent(filename1, filename2, info1, info2, msg1, msg2, nil, nil, isError)
}

func writeHtmlLineno(buf *bytes.Buffer, lineno, width int) {
	if lineno > 0 {
		fmt.Fprintf(buf, "<span class=\"lno\">%-*d </span>", width, lineno)
	} else {
		buf.WriteString("<span class=\"lno\"> </span>")
	}
}

func writeHtmlLinenoUnified(buf *bytes.Buffer, mode string, lineno1, lineno2, width int) {
	buf.WriteString("<span class=\"lno\">")

	if lineno1 > 0 {
		fmt.Fprintf(buf, "%-*d", width, lineno1)
	} else {
		fmt.Fprintf(buf, "%-*s", width, "")
	}

	if lineno2 > 0 {
		fmt.Fprintf(buf, " %-*d ", width, lineno2)
	} else {
		fmt.Fprintf(buf, " %-*s ", width, "")
	}

	buf.WriteString(mode)
	buf.WriteString(" </span>")
}

func writeHtmlLines(buf *bytes.Buffer, class string, lines [][]byte, lineno, linenoWidth int) {
	buf.WriteString("<span class=\"")
	buf.WriteString(class)
	buf.WriteString("\">")
	for _, line := range lines {
		lineno++
		writeHtmlLineno(buf, lineno, linenoWidth)
		writeHtmlBytes(buf, line)
		buf.WriteByte('\n')
	}
	buf.WriteString("</span>")
}

func writeHtmlLinesUnified(buf *bytes.Buffer, class string, mode string, lines [][]byte, start1, start2, linenoWidth int) {
	buf.WriteString("<span class=\"")
	buf.WriteString(class)
	buf.WriteString("\">")
	for _, line := range lines {
		if start1 >= 0 {
			start1++
		}
		if start2 >= 0 {
			start2++
		}
		writeHtmlLinenoUnified(buf, mode, start1, start2, linenoWidth)
		writeHtmlBytes(buf, line)
		buf.WriteByte('\n')
	}
	buf.WriteString("</span>")
}

func writeHtmlBlanks(buf *bytes.Buffer, n int) {
	buf.WriteString("<span class=\"nop\">")
	for n > 0 {
		buf.WriteString("<span class=\"lno\"> </span>\n")
		n--
	}
	buf.WriteString("</span>")
}

// Write single line with changes
func writeHtmlLineChange(buf *bytes.Buffer, line []byte, pos []int, change []bool) {
	inChg := false
	for i, end := 0, len(change); i < end; {
		j, c := i+1, change[i]
		for j < end && change[j] == c {
			j++
		}
		if c && !inChg {
			buf.WriteString("<span class=\"chg\">")
		} else if !c && inChg {
			buf.WriteString("</span>")
		}
		writeHtmlBytes(buf, line[pos[i]:pos[j]])
		i, inChg = j, c
	}
	if inChg {
		buf.WriteString("</span>")
	}
}

func htmlFileTable(outFmt *OutputFormat) {

	if !outFmt.headerPrinted {
		outAcquireLock()
		outFmt.headerPrinted = true
		out.WriteString("<table class=\"tab\"><tr><td class=\"tth\"><span class=\"hdr\">")
		out.WriteString(html.EscapeString(outFmt.name1))
		out.WriteString("</span>")
		if outFmt.fileInfo1 != nil {
			fmt.Fprintf(out, "<br><span class=\"inf\">%d %s</span>", outFmt.fileInfo1.Size(), outFmt.fileInfo1.ModTime().Format(time.RFC1123))
		}
		out.WriteString("</td><td class=\"tth\"><span class=\"hdr\">")
		out.WriteString(html.EscapeString(outFmt.name2))
		out.WriteString("</span>")
		if outFmt.fileInfo2 != nil {
			fmt.Fprintf(out, "<br><span class=\"inf\">%d %s</span>", outFmt.fileInfo2.Size(), outFmt.fileInfo2.ModTime().Format(time.RFC1123))
		}
		out.WriteString("</td></tr>")
	}
}

func htmlFileTableUnified(outFmt *OutputFormat) {

	if !outFmt.headerPrinted {
		outAcquireLock()
		outFmt.headerPrinted = true
		out.WriteString("<table class=\"tab\"><tr><td class=\"tth\"><span class=\"hdr\">")
		out.WriteString(html.EscapeString(outFmt.name1))
		out.WriteString("</span>")
		if outFmt.fileInfo1 != nil {
			fmt.Fprintf(out, " <span class=\"inf\">%d %s</span>", outFmt.fileInfo1.Size(), outFmt.fileInfo1.ModTime().Format(time.RFC1123))
		}
		out.WriteString("<br><span class=\"hdr\">")
		out.WriteString(html.EscapeString(outFmt.name2))
		out.WriteString("</span>")
		if outFmt.fileInfo2 != nil {
			fmt.Fprintf(out, " <span class=\"inf\">%d %s</span>", outFmt.fileInfo2.Size(), outFmt.fileInfo2.ModTime().Format(time.RFC1123))
		}
		out.WriteString("</td></tr>")
	}
}

func (chg *DiffChangerUnifiedHtml) diffLines(ops []DiffOp) {

	htmlFileTableUnified(chg.OutputFormat)
	chg.buf1.Reset()

	for _, v := range ops {
		switch v.op {
		case DiffOpInsert:
			writeHtmlLinesUnified(&chg.buf1, "add", "+", chg.file2[v.start2:v.end2], -1, v.start2, chg.linenoWidth)

		case DiffOpRemove:
			writeHtmlLinesUnified(&chg.buf1, "del", "-", chg.file1[v.start1:v.end1], v.start1, -1, chg.linenoWidth)

		case DiffOpModify:
			writeHtmlLinesUnified(&chg.buf1, "del", "-", chg.file1[v.start1:v.end1], v.start1, -1, chg.linenoWidth)
			writeHtmlLinesUnified(&chg.buf1, "add", "+", chg.file2[v.start2:v.end2], -1, v.start2, chg.linenoWidth)

		default:
			writeHtmlLinesUnified(&chg.buf1, "nop", " ", chg.file1[v.start1:v.end1], v.start1, v.start2, chg.linenoWidth)
		}
	}

	out.WriteString("<tr><td class=\"ttd\">")
	out.Write(chg.buf1.Bytes())
	out.WriteString("</td></tr>\n")
}

func (chg *DiffChangerHtml) diffLines(ops []DiffOp) {

	htmlFileTable(chg.OutputFormat)

	chg.buf1.Reset()
	chg.buf2.Reset()

	for _, v := range ops {
		switch v.op {
		case DiffOpInsert:
			writeHtmlBlanks(&chg.buf1, v.end2-v.start2)
			writeHtmlLines(&chg.buf2, "add", chg.file2[v.start2:v.end2], v.start2, chg.linenoWidth)

		case DiffOpRemove:
			writeHtmlLines(&chg.buf1, "del", chg.file1[v.start1:v.end1], v.start1, chg.linenoWidth)
			writeHtmlBlanks(&chg.buf2, v.end1-v.start1)

		case DiffOpModify:
			chg.buf1.WriteString("<span class=\"upd\">")
			chg.buf2.WriteString("<span class=\"upd\">")

			start1, start2 := v.start1, v.start2

			for start1 < v.end1 && start2 < v.end2 {

				writeHtmlLineno(&chg.buf1, start1+1, chg.linenoWidth)
				writeHtmlLineno(&chg.buf2, start2+1, chg.linenoWidth)

				if flagSuppressLineChanges {
					writeHtmlBytes(&chg.buf1, chg.file1[start1])
					writeHtmlBytes(&chg.buf2, chg.file2[start2])
				} else {
					// report on changes within the line
					line1, line2 := chg.file1[start1], chg.file2[start2]
					pos1, cmp1 := splitRunes(line1)
					pos2, cmp2 := splitRunes(line2)

					change1, change2 := doDiff(cmp1, cmp2)

					if change1 != nil {
						// perform shift boundaries, to make the changes more readable
						shiftBoundaries(cmp1, change1, runeBoundaryScore)
						shiftBoundaries(cmp2, change2, runeBoundaryScore)

						writeHtmlLineChange(&chg.buf1, line1, pos1, change1)
						writeHtmlLineChange(&chg.buf2, line2, pos2, change2)
					}
				}

				chg.buf1.WriteByte('\n')
				chg.buf2.WriteByte('\n')
				start1++
				start2++
			}

			chg.buf1.WriteString("</span>")
			chg.buf2.WriteString("</span>")

			if start1 < v.end1 {
				writeHtmlLines(&chg.buf1, "del", chg.file1[start1:v.end1], start1, chg.linenoWidth)
				writeHtmlBlanks(&chg.buf2, v.end1-start1)
			}

			if start2 < v.end2 {
				writeHtmlBlanks(&chg.buf1, v.end2-start2)
				writeHtmlLines(&chg.buf2, "add", chg.file2[start2:v.end2], start2, chg.linenoWidth)
			}

		default:
			n1, n2 := v.end1-v.start1, v.end2-v.start2
			maxN := maxInt(n1, n2)

			if n1 > 0 {
				writeHtmlLines(&chg.buf1, "nop", chg.file1[v.start1:v.end1], v.start1, chg.linenoWidth)
			}
			if n1 < maxN {
				writeHtmlBlanks(&chg.buf1, maxN-n1)
			}

			if n2 > 0 {
				writeHtmlLines(&chg.buf2, "nop", chg.file2[v.start2:v.end2], v.start2, chg.linenoWidth)
			}
			if n2 < maxN {
				writeHtmlBlanks(&chg.buf2, maxN-n2)
			}
		}
	}

	out.WriteString("<tr><td class=\"ttd\">")
	out.Write(chg.buf1.Bytes())
	out.WriteString("</td><td class=\"ttd\">")
	out.Write(chg.buf2.Bytes())
	out.WriteString("</td></tr>\n")

}

func (chg *DiffChangerUnifiedText) diffLines(ops []DiffOp) {

	if !chg.headerPrinted {
		outAcquireLock()
		chg.headerPrinted = true
		fmt.Fprintf(out, "--- %s\n", chg.name1)
		fmt.Fprintf(out, "+++ %s\n", chg.name2)
	}

	fmt.Fprintf(out, "@@ -%d,%d +%d,%d @@\n", ops[0].start1+1, ops[len(ops)-1].end1-ops[0].start1, ops[0].start2+1, ops[len(ops)-1].end2-ops[0].start2)

	for _, v := range ops {
		switch v.op {
		case DiffOpInsert, DiffOpRemove, DiffOpModify:
			for _, line := range chg.file1[v.start1:v.end1] {
				out.WriteString("- ")
				out.Write(line)
				out.WriteByte('\n')
			}

			for _, line := range chg.file2[v.start2:v.end2] {
				out.WriteString("+ ")
				out.Write(line)
				out.WriteByte('\n')
			}

		default:
			for _, line := range chg.file1[v.start1:v.end1] {
				out.WriteString("  ")
				out.Write(line)
				out.WriteByte('\n')
			}
		}
	}
}

func printLineNumbers(mode string, start1, end1, start2, end2 int) {
	if end1 < 0 || end1-start1 == 1 {
		fmt.Fprintf(out, "%d%s", start1+1, mode)
	} else {
		fmt.Fprintf(out, "%d,%d%s", start1+1, end1, mode)
	}
	if end2 < 0 || end2-start2 == 1 {
		fmt.Fprintf(out, "%d\n", start2+1)
	} else {
		fmt.Fprintf(out, "%d,%d\n", start2+1, end2)
	}
}

func (chg *DiffChangerText) diffLines(ops []DiffOp) {

	if !chg.headerPrinted {
		outAcquireLock()
		chg.headerPrinted = true
		fmt.Fprintf(out, "<<< %s\n", chg.name1)
		fmt.Fprintf(out, ">>> %s\n", chg.name2)
	}

	for _, v := range ops {
		switch v.op {
		case DiffOpSame:
			continue

		case DiffOpInsert:
			printLineNumbers("a", v.start1-1, -1, v.start2, v.end2)

		case DiffOpRemove:
			printLineNumbers("d", v.start1, v.end1, v.start2-1, -1)

		case DiffOpModify:
			printLineNumbers("c", v.start1, v.end1, v.start2, v.end2)
		}

		for _, line := range chg.file1[v.start1:v.end1] {
			out.WriteString("< ")
			out.Write(line)
			out.WriteByte('\n')
		}

		if v.end1 > v.start1 && v.end2 > v.start2 {
			out.WriteString("---\n")
		}

		for _, line := range chg.file2[v.start2:v.end2] {
			out.WriteString("> ")
			out.Write(line)
			out.WriteByte('\n')
		}
	}
}

// Test for space character
func isSpace(b byte) bool {
	return b == ' ' || b == '\t' || b == '\v' || b == '\f'
}

func skipSpaceRune(line []byte, i int) int {
	for i < len(line) {
		b, size := utf8.DecodeRune(line[i:])
		if !unicode.IsSpace(b) {
			return i
		}
		i += size
	}
	return i
}

// Get the next rune, and skip spaces after it
func getNextRuneNonspace(line []byte, i int) (rune, int) {
	b, size := utf8.DecodeRune(line[i:])
	return b, skipSpaceRune(line, i+size)
}

// Get the next rune, and determine if there is a space after it.
// Also ignore trailing spaces at end-of-line
func getNextRuneXspace(line []byte, i int) (rune, bool, int) {
	b, size := utf8.DecodeRune(line[i:])
	i += size
	spaceAfter := false
	for i < len(line) {
		s, size := utf8.DecodeRune(line[i:])
		if !unicode.IsSpace(s) {
			break
		}
		spaceAfter = true
		i += size
	}
	if spaceAfter && i >= len(line) {
		spaceAfter = false
	}
	return b, spaceAfter, i
}

func skipSpaceByte(line []byte, i int) int {
	for i < len(line) {
		if !isSpace(line[i]) {
			return i
		}
		i++
	}
	return i
}

func getNextByteNonSpace(line []byte, i int) (byte, int) {
	return line[i], skipSpaceByte(line, i+1)
}

func getNextByteXSpace(line []byte, i int) (byte, bool, int) {
	b, i := line[i], i+1
	spaceAfter := false
	for i < len(line) {
		if !isSpace(line[i]) {
			break
		}
		spaceAfter = true
		i++
	}
	if spaceAfter && i >= len(line) {
		spaceAfter = false
	}
	return b, spaceAfter, i
}

func compareLineBytes(line1, line2 []byte) bool {
	len1, len2 := len(line1), len(line2)
	var i, j int
	var v1, v2 byte
	switch {
	case flagCmpIgnoreAllSpace:
		i = skipSpaceByte(line1, 0)
		j = skipSpaceByte(line2, 0)
		for i < len1 && j < len2 {
			v1, i = getNextByteNonSpace(line1, i)
			v2, j = getNextByteNonSpace(line2, j)
			if flagCmpIgnoreCase && v1 != v2 {
				v1, v2 = toLowerByte(v1), toLowerByte(v2)
			}
			if v1 != v2 {
				return false
			}
		}
		if i < len1 || j < len2 {
			return false
		}

	case flagCmpIgnoreSpaceChange:
		var spaceAfter1, spaceAfter2 bool
		i = skipSpaceByte(line1, 0)
		j = skipSpaceByte(line2, 0)
		for i < len1 && j < len2 {
			v1, spaceAfter1, i = getNextByteXSpace(line1, i)
			v2, spaceAfter2, j = getNextByteXSpace(line2, j)
			if flagCmpIgnoreCase && v1 != v2 {
				v1, v2 = toLowerByte(v1), toLowerByte(v2)
			}
			if v1 != v2 || spaceAfter1 != spaceAfter2 {
				return false
			}
		}
		if i < len1 || j < len2 {
			return false
		}

	case flagCmpIgnoreCase:
		if len1 != len2 {
			return false
		}
		for i < len1 && j < len2 {
			if toLowerByte(line1[i]) != toLowerByte(line2[j]) {
				return false
			}
			i, j = i+1, j+1
		}
		if i < len1 || j < len2 {
			return false
		}
	}
	return true
}

func compareLineUnicode(line1, line2 []byte) bool {
	len1, len2 := len(line1), len(line2)
	var i, j int
	var v1, v2 rune
	var size1, size2 int
	switch {
	case flagCmpIgnoreAllSpace:
		i = skipSpaceRune(line1, 0)
		j = skipSpaceRune(line2, 0)
		for i < len1 && j < len2 {
			v1, i = getNextRuneNonspace(line1, i)
			v2, j = getNextRuneNonspace(line2, j)
			if flagCmpIgnoreCase && v1 != v2 {
				v1, v2 = unicode.ToLower(v1), unicode.ToLower(v2)
			}
			if v1 != v2 {
				return false
			}
		}
		if i < len1 || j < len2 {
			return false
		}

	case flagCmpIgnoreSpaceChange:
		i = skipSpaceRune(line1, 0)
		j = skipSpaceRune(line2, 0)
		var spaceAfter1, spaceAfter2 bool
		for i < len1 && j < len2 {
			v1, spaceAfter1, i = getNextRuneXspace(line1, i)
			v2, spaceAfter2, j = getNextRuneXspace(line2, j)
			if flagCmpIgnoreCase && v1 != v2 {
				v1, v2 = unicode.ToLower(v1), unicode.ToLower(v2)
			}
			if v1 != v2 || spaceAfter1 != spaceAfter2 {
				return false
			}
		}
		if i < len1 || j < len2 {
			return false
		}

	case flagCmpIgnoreCase:
		if len1 != len2 {
			return false
		}
		for i < len1 && j < len2 {
			v1, size1 = utf8.DecodeRune(line1[i:])
			v2, size2 = utf8.DecodeRune(line2[j:])
			if v1 != v2 && unicode.ToLower(v1) != unicode.ToLower(v2) {
				return false
			}
			i, j = i+size1, j+size2
		}
		if i < len1 || j < len2 {
			return false
		}
	}
	return true
}

var crcTable = crc32.MakeTable(crc32.Castagnoli)

func hash32(h uint32, b byte) uint32 {
	return crcTable[byte(h)^b] ^ (h >> 8)
}

func hash32Unicode(h uint32, r rune) uint32 {
	for r != 0 {
		h = hash32(h, byte(r))
		r = r >> 8
	}
	return h
}

func computeHashExact(data []byte) uint32 {
	// On amd64, this will be using the SSE4.2 hardware instructions, much faster!
	return crc32.Update(0, crcTable, data)
}

func computeHashBytes(line1 []byte) uint32 {
	var hash uint32
	switch {
	case flagCmpIgnoreAllSpace:
		for _, v1 := range line1 {
			if !isSpace(v1) {
				if flagCmpIgnoreCase {
					v1 = toLowerByte(v1)
				}
				hash = hash32(hash, v1)
			}
		}

	case flagCmpIgnoreSpaceChange:
		lastHash := hash
		lastSpace := true
		for _, v1 := range line1 {
			if isSpace(v1) {
				if !lastSpace {
					lastHash = hash
					hash = hash32(hash, ' ')
				}
				lastSpace = true
			} else {
				if flagCmpIgnoreCase {
					v1 = toLowerByte(v1)
				}
				hash = hash32(hash, v1)
				lastSpace = false
			}
		}
		if lastSpace {
			hash = lastHash
		}

	case flagCmpIgnoreCase:
		for _, v1 := range line1 {
			v1 = toLowerByte(v1)
			hash = hash32(hash, v1)
		}

	}
	return hash
}

func computeHashUnicode(line1 []byte) uint32 {
	var hash uint32
	i, len1 := 0, len(line1)

	switch {
	case flagCmpIgnoreAllSpace:
		for i < len1 {
			v1, size := utf8.DecodeRune(line1[i:])
			i = i + size
			if !unicode.IsSpace(v1) {
				if flagCmpIgnoreCase {
					v1 = unicode.ToLower(v1)
				}
				hash = hash32Unicode(hash, v1)
			}
		}

	case flagCmpIgnoreSpaceChange:
		lastHash := hash
		lastSpace := true
		for i < len1 {
			v1, size := utf8.DecodeRune(line1[i:])
			i += size
			if unicode.IsSpace(v1) {
				if !lastSpace {
					lastHash = hash
					hash = hash32(hash, ' ')
				}
				lastSpace = true
			} else {
				if flagCmpIgnoreCase {
					v1 = unicode.ToLower(v1)
				}
				hash = hash32Unicode(hash, v1)
				lastSpace = false
			}
		}
		if lastSpace {
			hash = lastHash
		}

	case flagCmpIgnoreCase:
		for i < len1 {
			v1, size := utf8.DecodeRune(line1[i:])
			i = i + size
			v1 = unicode.ToLower(v1)
			hash = hash32Unicode(hash, v1)
		}
	}
	return hash
}

type EquivClass struct {
	id   int
	hash uint32
	line *[]byte
	next *EquivClass
}

type LinesData struct {
	ids       []int // Ids for each line,
	zidS      []int // list of ids with unmatched lines replaced by a single entry (and blank lines removed)
	zCount    []int // Number of lines that represent each zidS entry
	change    []bool
	zidsStart int
	zidsEnd   int
}

// Compute id's that represent the original lines, these numeric id's are use for faster line comparison.
func findEquivLines(lines1, lines2 [][]byte) (*LinesData, *LinesData) {

	info1 := LinesData{
		ids:    make([]int, len(lines1)),
		change: make([]bool, len(lines1)),
	}

	info2 := LinesData{
		ids:    make([]int, len(lines2)),
		change: make([]bool, len(lines2)),
	}

	// since we already have a hashing function, it's faster to use arrays than to use go's builtin map
	// Use bucket size that is power of 2
	buckets := 1 << 9
	for buckets < (len(lines1)+len(lines2))*2 {
		buckets = buckets << 1
	}

	// create the slice we are using for hash tables
	eqHash := make([]*EquivClass, buckets)

	// Use id=0 for blank lines.
	// Later in report_changes(), do not report changes on chunks of lines with id=0
	if flagCmpIgnoreBlankLines {
		hashcode := computeHash(blankLine)
		iHash := int(hashcode) & (buckets - 1)
		eqHash[iHash] = &EquivClass{id: 0, line: &blankLine, hash: hashcode}
	}

	// the unique id for identical lines, start with 1.
	var maxIdF1, maxIdF2 int
	nextId := 1

	// process both sets of lines
	for findEx := 0; findEx < 2; findEx++ {
		var lines [][]byte
		var ids []int

		if findEx == 0 {
			lines = lines1
			ids = info1.ids
		} else {
			lines = lines2
			ids = info2.ids
		}

		for i := 0; i < len(lines); i++ {
			lPtr := &lines[i]
			// find current line in eqHash
			hashcode := computeHash(*lPtr)
			iHash := int(hashcode) & (buckets - 1)
			eq := eqHash[iHash]
			if eq == nil {
				// not found in eqHash, create new entry
				ids[i] = nextId
				eqHash[iHash] = &EquivClass{id: nextId, line: lPtr, hash: hashcode}
				nextId++
			} else if eq.hash == hashcode && compareLine(*lPtr, *eq.line) {
				// found, and line is the same. reuse same id
				ids[i] = eq.id
			} else {
				// hash-collision. look through link-list for same match
				n := eq.next
				for n != nil {
					if n.hash == hashcode && compareLine(*lPtr, *n.line) {
						ids[i] = n.id
						break
					}
					n = n.next
				}
				// new entry, link to start of linked-list
				if n == nil {
					ids[i] = nextId
					eq.next = &EquivClass{id: nextId, line: lPtr, hash: hashcode, next: eq.next}
					nextId++
				}
			}
		}

		if findEx == 0 {
			maxIdF1 = nextId - 1
		} else {
			maxIdF2 = nextId - 1
		}
	}

	compressEquivIds(&info1, &info2, maxIdF1, maxIdF2)

	return &info1, &info2
}

// Count the occurrences of each unique ids in both sets of lines, we will then know which lines are only present in one file, but not the other.
// Remove chunks of lines that do not appear in the other files, and replace with a single entry
// Return compressed lists of ids and a list indicating where are the chunk of lines being replaced
func compressEquivIds(lines1, lines2 *LinesData, maxId1, maxId2 int) {

	len1, len2 := len(lines1.ids), len(lines2.ids)
	hasIds1, hasIds2 := make([]bool, maxId1+1), make([]bool, maxId2+1)

	// Determine which id's are in each file
	for _, v := range lines1.ids {
		hasIds1[v] = true
	}
	for _, v := range lines2.ids {
		hasIds2[v] = true
	}

	// exclude lines from the beginning that are identical in both files
	// if line in file1 but not in file2, exclude it and marked as changed
	// if line in file2 but not in file1, exclude it and marked as changed
	i1, i2 := 0, 0
	for i1 < len1 && i2 < len2 {
		v1, v2 := lines1.ids[i1], lines2.ids[i2]
		if v1 > maxId2 || !hasIds2[v1] {
			lines1.change[i1] = true
			i1++
		} else if v2 > maxId1 || !hasIds1[v2] {
			lines2.change[i2] = true
			i2++
		} else if v1 == v2 {
			i1++
			i2++
		} else {
			break
		}
	}

	// exclude lines from the end that are identical in both files
	// if line in file1 but not in file2, exclude it and marked as changed
	// if line in file2 but not in file1, exclude it and marked as changed
	j1, j2 := len1, len2
	for i1 < j1 && i2 < j2 {
		v1, v2 := lines1.ids[j1-1], lines2.ids[j2-1]
		if v1 > maxId2 || !hasIds2[v1] {
			j1--
			lines1.change[j1] = true
		} else if v2 > maxId1 || !hasIds1[v2] {
			j2--
			lines2.change[j2] = true
		} else if v1 == v2 {
			j1--
			j2--
		} else {
			break
		}
	}

	// One of the list is now empty, no need to run diff algorithm for comparison.
	// Just mark the remaining lines other list as changed.
	if i1 == j1 {
		for i2 < j2 {
			lines2.change[i2] = true
			i2++
		}
		return
	}
	if i2 == j2 {
		for i1 < j1 {
			lines1.change[i1] = true
			i1++
		}
		return
	}

	// store excluded lines from beginning and end of file
	lines1.zidsStart, lines1.zidsEnd = i1, j1
	lines2.zidsStart, lines2.zidsEnd = i2, j2

	// Go through all lines, replace chunk of lines that does not exists in the
	// other set with a single entry and a negative new id).
	nextId := maxInt(maxId1, maxId2) + 1
	for findEx := 0; findEx < 2; findEx++ {
		var ids []int
		var hasIds []bool
		var maxId int

		if findEx == 0 {
			ids = lines1.ids[lines1.zidsStart:lines1.zidsEnd]
			hasIds = hasIds2
			maxId = maxId2
		} else {
			ids = lines2.ids[lines2.zidsStart:lines2.zidsEnd]
			hasIds = hasIds1
			maxId = maxId1
		}

		// new slices for compressed ids and the number of lines each entry replaced
		// use a new negative id for those merged lines
		zCount := make([]int, len(ids))
		zids := make([]int, len(ids))

		lastExclude := false
		n := 0
		for _, v := range ids {
			exclude := v > maxId || !hasIds[v]
			if exclude && lastExclude {
				zCount[n-1]++
				zids[n-1] = -nextId
				nextId++
			} else if exclude {
				zCount[n]++
				zids[n] = -v
				n++
			} else {
				zCount[n]++
				zids[n] = v
				n++
			}
			lastExclude = exclude
		}

		// shrink the slice
		zids = zids[:n]
		zCount = zCount[:n]

		if findEx == 0 {
			lines1.zidS = zids
			lines1.zCount = zCount
		} else {
			lines2.zidS = zids
			lines2.zCount = zCount
		}
	}
}

// Do the reverse of the compressEquivIds.
// zLines1 and zLines2 contains the 'extra' lines each entry represents.
func expandChangeList(info1, info2 *LinesData, zChange1, zChange2 []bool) {

	for findEx := 0; findEx < 2; findEx++ {
		var info *LinesData
		var change, zChange []bool

		// expand the changes into the range between zids_start and zids_end
		if findEx == 0 {
			info = info1
			change = info1.change[info1.zidsStart:]
			zChange = zChange1
		} else {
			info = info2
			change = info2.change[info2.zidsStart:]
			zChange = zChange2
		}

		// no change
		if zChange == nil {
			continue
		}

		// expand each entry by the number of lines in zCount[]
		n := 0
		for i, m := range info.zCount {
			if zChange[i] {
				for end := n + m; n < end; n++ {
					change[n] = true
				}
			} else {
				n += m
			}
		}
	}
}

// open file, and read/mmap the entire content into byte array
func openFile(fName string, fInfo os.FileInfo) *FileData {

	file := &FileData{name: fName, info: fInfo}
	fSize := file.info.Size()

	var err error

	if fSize >= 1e8 {
		file.errorMsg = MsgFileTooBig
		return file
	}

	// zero size file.
	if fSize <= 0 {
		return file
	}

	// open the file
	file.osFile, err = os.Open(file.name)
	if err != nil {
		file.osFile = nil
		file.errorMsg = err.Error()
		return file
	}

	if strings.HasSuffix(fName, ".gz") {
		// Uncompressed .gz file
		reader, err := gzip.NewReader(file.osFile)
		if err != nil {
			file.errorMsg = err.Error()
			return file
		}
		fData, err := io.ReadAll(reader)
		if err != nil {
			file.errorMsg = err.Error()
			return file
		}
		reader.Close()
		file.data = fData
		file.osFile.Close()
		file.osFile = nil
	} else if strings.HasSuffix(fName, ".bz2") {
		// Uncompressed .bz2 file
		reader := bzip2.NewReader(file.osFile)
		fData, err := io.ReadAll(reader)
		if err != nil {
			file.errorMsg = err.Error()
			return file
		}
		file.data = fData
		file.osFile.Close()
		file.osFile = nil
	} else if has_mmap && fSize > MmapThreshold {
		// map to file into memory, leave file open.
		file.data, err = map_file(file.osFile, 0, int(fSize))
		if err != nil {
			file.osFile.Close()
			file.osFile = nil
			file.errorMsg = err.Error()
			return file
		}
		file.isMapped = true
	} else {
		// read in the entire file

		fData := make([]byte, fSize)
		n, err := file.osFile.Read(fData)
		if err != nil {
			file.errorMsg = err.Error()
			return file
		}
		file.data = fData[:n]
		// close file
		file.osFile.Close()
		file.osFile = nil
	}

	return file
}

// Close file (and unmap it)
func (file *FileData) closeFile() {
	if file.osFile != nil {
		if file.isMapped && file.data != nil {
			unmap_file(file.data)
		}
		file.osFile.Close()
		file.osFile = nil
	}
	file.data = nil
}

// check if file is binary
func (file *FileData) checkBinary() {
	if file.data == nil {
		return
	}
	if len(file.data) == 0 {
		file.data = nil
		file.errorMsg = MsgFileSizeZero
		return
	}
	if bytes.IndexByte(file.data[0:minInt(len(file.data), BinaryCheckSize)], 0) >= 0 {
		file.data = nil
		file.errorMsg = MsgFileIsBinary
		return
	}
}

// split up data into text lines
func (file *FileData) splitLines() [][]byte {

	lines := make([][]byte, 0, minInt(len(file.data)/32, 500))
	var i, prevI int
	var b, lastB byte

	data := file.data
	for i, b = range data {
		// accept dos, unix, mac newline
		if b == '\n' && lastB == '\r' {
			prevI = i + 1
		} else if b == '\n' || b == '\r' {
			lines = append(lines, data[prevI:i])
			prevI = i + 1
		} else if b == 0 && i < BinaryCheckSize {
			file.isBinary = true
			file.errorMsg = MsgFileIsBinary
			return nil
		}
		lastB = b
	}

	// add last incomplete line (if required)
	if len(data) > prevI {
		lines = append(lines, data[prevI:])
	}

	return lines
}

// FileInfoList for sorting os.FileInfo by name
type FileInfoList []os.FileInfo

func (s FileInfoList) Len() int           { return len(s) }
func (s FileInfoList) Swap(i, j int)      { s[i], s[j] = s[j], s[i] }
func (s FileInfoList) Less(i, j int) bool { return s[i].Name() < s[j].Name() }

// get a list of sorted directory entries
func readSortedDir(dirname string) ([]os.FileInfo, error) {

	dir, err := os.Open(dirname)
	if err != nil {
		return nil, err
	}

	all, err := dir.Readdir(-1)
	if err != nil {
		dir.Close()
		return nil, err
	}

	dir.Close()

	// Exclude files
	if regexpExcludeFiles != nil && len(all) > 0 {
		eAll := make([]os.FileInfo, 0, len(all))
		for _, f := range all {
			if !regexpExcludeFiles.MatchString(f.Name()) {
				eAll = append(eAll, f)
			}
		}
		all = eAll
	}

	sort.Sort(FileInfoList(all))

	return all, nil
}

// compare 2 dirs.
func diffDirs(dirname1, dirname2 string, finfo1, finfo2 os.FileInfo) {

	dirname1 = strings.TrimRight(dirname1, PathSeparator)
	dirname2 = strings.TrimRight(dirname2, PathSeparator)

	dir1, err1 := readSortedDir(dirname1)
	dir2, err2 := readSortedDir(dirname2)

	if err1 != nil || err2 != nil {
		msg1, msg2 := "", ""
		if err1 != nil {
			msg1 = err1.Error()
		}
		if err2 != nil {
			msg2 = err2.Error()
		}
		outputDiffMessage(dirname1, dirname2, finfo1, finfo2, msg1, msg2, true)
		return
	}

	// Loop through all files, then all directories
	for _, dirMode := range []bool{false, true} {
		i1, i2 := 0, 0
		for i1 < len(dir1) || i2 < len(dir2) {
			name1, name2 := "", ""
			if i1 < len(dir1) {
				name1 = dir1[i1].Name()
				if dir1[i1].IsDir() != dirMode || strings.HasPrefix(name1, ".") {
					i1++
					continue
				}
			}
			if i2 < len(dir2) {
				name2 = dir2[i2].Name()
				if dir2[i2].IsDir() != dirMode || strings.HasPrefix(name2, ".") {
					i2++
					continue
				}
			}

			if name1 == name2 {
				if dir1[i1].IsDir() != dir2[i2].IsDir() {
					if !dirMode {
						if dir1[i1].IsDir() {
							outputDiffMessage(dirname1+PathSeparator+name1, dirname2+PathSeparator+name2, dir1[i1], dir2[i2], MsgThisIsDir, MsgThisIsFile, true)
						} else {
							outputDiffMessage(dirname1+PathSeparator+name1, dirname2+PathSeparator+name2, dir1[i1], dir2[i2], MsgThisIsFile, MsgThisIsDir, true)
						}
					}
				} else if dirMode {
					// compare sub-directories
					diffDirs(dirname1+PathSeparator+name1, dirname2+PathSeparator+name2, dir1[i1], dir2[i2])
				} else {
					// compare files
					if flagMaxGoroutines > 1 {
						queueDiffFile(dirname1+PathSeparator+name1, dirname2+PathSeparator+name2, dir1[i1], dir2[i2])
					} else {
						diffFile(dirname1+PathSeparator+name1, dirname2+PathSeparator+name2, dir1[i1], dir2[i2])
					}
				}
				i1, i2 = i1+1, i2+1
			} else if (i1 < len(dir1) && name1 < name2) || i2 >= len(dir2) {
				if dirMode {
					outputDiffMessage(dirname1+PathSeparator+name1, dirname2+PathSeparator+name1, dir1[i1], nil, "", MsgDirNotExists, true)
				} else {
					if flagSuppressMissingFile {
						outputDiffMessage(dirname1+PathSeparator+name1, dirname2+PathSeparator+name1, dir1[i1], nil, "", MsgFileNotExists, true)
					} else {
						fData := openFile(dirname1+PathSeparator+name1, dir1[i1])
						fData.checkBinary()
						outputDiffMessageContent(dirname1+PathSeparator+name1, dirname2+PathSeparator+name1, dir1[i1], nil, fData.errorMsg, MsgFileNotExists, fData.splitLines(), nil, true)
						fData.closeFile()
					}
				}
				i1++
			} else if (i2 < len(dir2) && name2 < name1) || i1 >= len(dir1) {
				if dirMode {
					outputDiffMessage(dirname1+PathSeparator+name2, dirname2+PathSeparator+name2, nil, dir2[i2], MsgDirNotExists, "", true)
				} else {
					if flagSuppressMissingFile {
						outputDiffMessage(dirname1+PathSeparator+name2, dirname2+PathSeparator+name2, nil, dir2[i2], MsgFileNotExists, "", true)
					} else {
						fData := openFile(dirname2+PathSeparator+name2, dir2[i2])
						fData.checkBinary()
						outputDiffMessageContent(dirname1+PathSeparator+name2, dirname2+PathSeparator+name2, nil, dir2[i2], MsgFileNotExists, fData.errorMsg, nil, fData.splitLines(), true)
						fData.closeFile()
					}
				}
				i2++
			} else {
				break
			}
		}
	}
}

// compare 2 file
func diffFile(filename1, filename2 string, fInfo1, fInfo2 os.FileInfo) {

	file1 := openFile(filename1, fInfo1)
	file2 := openFile(filename2, fInfo2)

	defer file1.closeFile()
	defer file2.closeFile()

	if file1.errorMsg != "" || file2.errorMsg != "" {
		// display error messages
		outputDiffMessage(filename1, filename2, fInfo1, fInfo2, file1.errorMsg, file2.errorMsg, true)
		return
	} else if bytes.Equal(file1.data, file2.data) {
		// files are equal
		if flagShowIdenticalFiles {
			outputDiffMessage(filename1, filename2, fInfo1, fInfo2, MsgFileIdentical, MsgFileIdentical, false)
		}
		return
	}

	lines1 := file1.splitLines()
	lines2 := file2.splitLines()

	if file1.isBinary || file2.isBinary {

		var msg1, msg2 string

		if file1.isBinary {
			msg1 = MsgBinFileDiffers
		} else {
			msg1 = MsgFileDiffers
		}

		if file2.isBinary {
			msg2 = MsgBinFileDiffers
		} else {
			msg2 = MsgFileDiffers
		}

		if msg1 != "" || msg2 != "" {
			outputDiffMessage(filename1, filename2, fInfo1, fInfo2, msg1, msg2, true)
		}
	} else {
		// Compute equiv ids for each line.
		info1, info2 := findEquivLines(lines1, lines2)

		// No zidS available, no need to run diff comparison algorithm
		// The find_equiv_lines() function may have performed the comparison already.
		if info1.zidS != nil && info2.zidS != nil {
			// run the diff algorithm
			zChange1, zChange2 := doDiff(info1.zidS, info2.zidS)

			// expand the change list, so that change array contains changes to actual lines
			expandChangeList(info1, info2, zChange1, zChange2)
		}

		// perform shift boundary
		shiftBoundaries(info1.ids, info1.change, nil)
		shiftBoundaries(info2.ids, info2.change, nil)

		chgData := DiffChangerData{
			OutputFormat: &OutputFormat{
				name1:       filename1,
				name2:       filename2,
				fileInfo1:   fInfo1,
				fileInfo2:   fInfo2,
				linenoWidth: len(fmt.Sprintf("%d", maxInt(len(lines1), len(lines2)))),
			},
			file1: lines1,
			file2: lines2,
		}

		var chg DiffChanger

		// Choose change output format: text or html
		if flagOutputAsText {
			if flagUnifiedContext {
				chg = &DiffChangerUnifiedText{DiffChangerData: chgData}
			} else {
				chg = &DiffChangerText{DiffChangerData: chgData}
			}
		} else {
			if flagUnifiedContext {
				chg = &DiffChangerUnifiedHtml{DiffChangerData: chgData}
			} else {
				chg = &DiffChangerHtml{DiffChangerData: chgData}
			}
		}

		// output diff results
		changed := reportDiff(chg, info1.ids, info2.ids, info1.change, info2.change)

		if chgData.headerPrinted {
			if !flagOutputAsText {
				out.WriteString("</table><br>\n")
			}
			chgData.headerPrinted = false
			outReleaseLock()
		}

		if !changed && flagShowIdenticalFiles {
			// report on identical file if required
			outputDiffMessage(filename1, filename2, fInfo1, fInfo2, MsgFileIdentical, MsgFileIdentical, false)
		}
	}
}

// shortcut functions. hopefully will be inlined by compiler
func maxInt(a, b int) int {
	if a < b {
		return b
	}
	return a
}

// shortcut functions. hopefully will be inlined by compiler
func minInt(a, b int) int {
	if a < b {
		return a
	}
	return b
}

// An O(ND) Difference Algorithm: Find middle snake
func algorithmSms(data1, data2 []int, v []int) (int, int, int, int) {

	end1, end2 := len(data1), len(data2)
	mMax := end1 + end2 + 1
	upK := end1 - end2
	odd := (upK & 1) != 0
	downOff, upOff := mMax, mMax-upK+mMax+mMax+2

	v[downOff+1] = 0
	v[downOff] = 0
	v[upOff+upK-1] = end1
	v[upOff+upK] = end1

	var k, x, u, z int

	for d := 1; true; d++ {
		upKPlusD := upK + d
		upKMinusD := upK - d
		for k = -d; k <= d; k += 2 {
			x = v[downOff+k+1]
			if k > -d && (k == d || z >= x) {
				x, z = z+1, x
			} else {
				z = x
			}
			for u = x; x < end1 && x-k < end2 && data1[x] == data2[x-k]; x++ {
			}
			if odd && (upKMinusD < k) && (k < upKPlusD) && v[upOff+k] <= x {
				return u, u - k, x, x - k
			}
			v[downOff+k] = x
		}
		z = v[upOff+upKMinusD-1]
		for k = upKMinusD; k <= upKPlusD; k += 2 {
			x = z
			if k < upKPlusD {
				z = v[upOff+k+1]
				if k == upKMinusD || z <= x {
					x = z - 1
				}
			}
			for u = x; x > 0 && x > k && data1[x-1] == data2[x-k-1]; x-- {
			}
			if !odd && (-d <= k) && (k <= d) && x <= v[downOff+k] {
				return x, x - k, u, u - k
			}
			v[upOff+k] = x
		}
	}
	return 0, 0, 0, 0 // should not reach here
}

// Special case for algorithmSms() with only 1 item.
func findOneSms(value int, list []int) (int, int) {
	for i, v := range list {
		if v == value {
			return 0, i
		}
	}
	return 1, 0
}

// An O(ND) Difference Algorithm: Find LCS
func algorithmLcs(data1, data2 []int, change1, change2 []bool, v []int) {

	start1, start2 := 0, 0
	end1, end2 := len(data1), len(data2)

	// matches found at start and end of list
	for start1 < end1 && start2 < end2 && data1[start1] == data2[start2] {
		start1++
		start2++
	}
	for start1 < end1 && start2 < end2 && data1[end1-1] == data2[end2-1] {
		end1--
		end2--
	}

	len1, len2 := end1-start1, end2-start2

	switch {
	case len1 == 0:
		for start2 < end2 {
			change2[start2] = true
			start2++
		}

	case len2 == 0:
		for start1 < end1 {
			change1[start1] = true
			start1++
		}

	case len1 == 1 && len2 == 1:
		change1[start1] = true
		change2[start2] = true

	default:
		data1, change1 = data1[start1:end1], change1[start1:end1]
		data2, change2 = data2[start2:end2], change2[start2:end2]

		var x0, y0, x1, y1 int

		if len(data1) == 1 {
			// match one item, use simple search function
			x0, y0 = findOneSms(data1[0], data2)
			x1, y1 = x0, y0
		} else if len(data2) == 1 {
			// match one item, use simple search function
			y0, x0 = findOneSms(data2[0], data1)
			x1, y1 = x0, y0
		} else {
			// Find a point with the longest common sequence
			x0, y0, x1, y1 = algorithmSms(data1, data2, v)
		}

		// Use the partitions to split this problem into subproblems.
		algorithmLcs(data1[:x0], data2[:y0], change1[:x0], change2[:y0], v)
		algorithmLcs(data1[x1:], data2[y1:], change1[x1:], change2[y1:], v)
	}
}

// Perform the shift
func doShiftBoundary(start, end, offset int, change []bool) {
	if offset < 0 {
		for offset != 0 {
			start, end, offset = start-1, end-1, offset+1
			change[start], change[end] = true, false
		}
	} else {
		for offset != 0 {
			change[start], change[end] = false, true
			start, end, offset = start+1, end+1, offset-1
		}
	}
}

// Determine if the changes starting at 'pos' can be shifted 'up' or 'down'
func findShiftBoundary(start int, data []int, change []bool) (int, int, int, bool, bool) {
	end, dLen := start+1, len(data)
	up, down := 0, 0

	// Find the end of this chunk of changes
	for end < dLen && change[end] {
		end++
	}

	for start-up-1 >= 0 && !change[start-up-1] && data[start-up-1] == data[end-up-1] {
		up = up + 1
	}

	for end+down < dLen && !change[end+down] && data[end+down] == data[start+down] {
		down = down + 1
	}

	// has changes been shifted to start/end of list or merged with previous/next change
	upMerge := (start-up == 0) || change[start-up-1]
	downMerge := (end+down == dLen) || change[end+down]

	return end, up, down, upMerge, downMerge
}

// scoring function for shifting characters in a line.
func runeEdgeScore(r rune) int {

	switch r {
	case ' ', '\t', '\v', '\f':
		return 100

	case '<', '>', '(', ')', '[', ']', '\'', '"':
		return 40
	}

	return 0
}

// scoring character boundary, for finding a change chunk that is easier to read
func runeBoundaryScore(r1, r2 int) int {

	s1 := runeEdgeScore(rune(r1))
	s2 := runeEdgeScore(rune(r2))

	return s1 + s2
}

// shift changes up or down to make it more readable.
func shiftBoundaries(data []int, change []bool, boundaryScore func(int, int) int) {

	start, clen := 0, len(change)

	for start < clen {
		// find the next chunk of changes
		for start < clen && !change[start] {
			start++
		}
		if start >= clen {
			break
		}

		// find the limit of where this set of changes can be shifted
		end, up, down, upMerge, downMerge := findShiftBoundary(start, data, change)

		// The chunk is already at the start, do not shift downwards
		if start == 0 {
			up, down = 0, 0
		}

		switch {
		case up > 0 && upMerge:
			// shift up, merged with previous chunk of changes
			doShiftBoundary(start, end, -up, change)
			// restart at the beginning of this merged chunk
			nStart := start
			for nStart -= up; nStart-1 >= 0 && change[nStart-1]; nStart-- {
			}
			if nStart > 0 {
				start = nStart
			}

		case down > 0 && downMerge:
			// shift down, merged with next chunk of changes
			doShiftBoundary(start, end, down, change)
			start += down

		case (up > 0 || down > 0) && boundaryScore != nil:
			// Only perform shifts when there is a boundary score function
			offset, bestScore := 0, boundaryScore(data[start], data[end-1])
			for i := -up; i <= down; i++ {
				if i != 0 {
					score := boundaryScore(data[start+i], data[end+i-1])
					if score > bestScore {
						offset, bestScore = i, score
					}
				}
			}
			if offset != 0 {
				doShiftBoundary(start, end, offset, change)
			}
			start = end
			if offset > 0 {
				start += offset
			}

		default:
			// no shift
			start = end
		}
	}
}

// Wait for all jobs to finish
func jobQueueFinish() {
	if flagMaxGoroutines > 1 {
		jobWait.Wait()
	}
}

// Initialise job queues
func jobQueueInit() {

	if flagMaxGoroutines > 1 {

		if flagMaxGoroutines > runtime.GOMAXPROCS(-1) {
			runtime.GOMAXPROCS(flagMaxGoroutines)
		}

		// create async job queue channel
		jobQueue = make(chan JobQueue, 1)

		// start up goroutines, to handle file comparison
		for i := 0; i < flagMaxGoroutines; i++ {
			go func() {
				for job := range jobQueue {
					diffFile(job.name1, job.name2, job.info1, job.info2)
					jobWait.Done()
				}
			}()
		}
	}
}

// Queue file comparison task
func queueDiffFile(fName1, fName2 string, finfo1, finfo2 os.FileInfo) {
	jobWait.Add(1)
	jobQueue <- JobQueue{
		name1: fName1,
		name2: fName2,
		info1: finfo1,
		info2: finfo2,
	}
}

// Acquire Mutex lock on output stream
func outAcquireLock() {
	if flagMaxGoroutines > 1 {
		outLock.Lock()
	}
}

// Release Mutex lock on output stream
func outReleaseLock() {
	if flagMaxGoroutines > 1 {
		outLock.Unlock()
	}
}
