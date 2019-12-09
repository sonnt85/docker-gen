package dockergen

import (
	"bytes"
	"crypto/sha1"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"io/ioutil"
	"log"
	"net/url"
	"os"
	"path/filepath"
	"reflect"
	"regexp"
	"strconv"
	"strings"
	"syscall"
	"text/template"
	"encoding/base32"
	"encoding/base64"
	util "github.com/Masterminds/goutils"
//    "github.com/Masterminds/sprig"
)
// returns map of environment variables
func readEnv() (env map[string]string) {
	env = make(map[string]string)
	for _, setting := range os.Environ() {
		pair := strings.SplitN(setting, "=", 2)
		env[pair[0]] = pair[1]
	}
	return
}

// custom function that returns key, value for all environment variable keys matching prefix
// (see original envtpl: https://pypi.org/project/envtpl/)
func environment(prefix string) map[string]string {
	env := make(map[string]string)
	for _, setting := range os.Environ() {
		pair := strings.SplitN(setting, "=", 2)
		if strings.HasPrefix(pair[0], prefix) {
			env[pair[0]] = pair[1]
		}
	}
	return env
}

func regexMatch(regex string, s string) bool {
	match, _ := regexp.MatchString(regex, s)
	return match
}

func mustRegexMatch(regex string, s string) (bool, error) {
	return regexp.MatchString(regex, s)
}

func regexFindAll(regex string, s string, n int) []string {
	r := regexp.MustCompile(regex)
	return r.FindAllString(s, n)
}

func mustRegexFindAll(regex string, s string, n int) ([]string, error) {
	r, err := regexp.Compile(regex)
	if err != nil {
		return []string{}, err
	}
	return r.FindAllString(s, n), nil
}

func regexFind(regex string, s string) string {
	r := regexp.MustCompile(regex)
	return r.FindString(s)
}

func mustRegexFind(regex string, s string) (string, error) {
	r, err := regexp.Compile(regex)
	if err != nil {
		return "", err
	}
	return r.FindString(s), nil
}

func regexReplaceAll(regex string, s string, repl string) string {
	r := regexp.MustCompile(regex)
	return r.ReplaceAllString(s, repl)
}

func mustRegexReplaceAll(regex string, s string, repl string) (string, error) {
	r, err := regexp.Compile(regex)
	if err != nil {
		return "", err
	}
	return r.ReplaceAllString(s, repl), nil
}

func regexReplaceAllLiteral(regex string, s string, repl string) string {
	r := regexp.MustCompile(regex)
	return r.ReplaceAllLiteralString(s, repl)
}

func mustRegexReplaceAllLiteral(regex string, s string, repl string) (string, error) {
	r, err := regexp.Compile(regex)
	if err != nil {
		return "", err
	}
	return r.ReplaceAllLiteralString(s, repl), nil
}

func regexSplit(regex string, s string, n int) []string {
	r := regexp.MustCompile(regex)
	return r.Split(s, n)
}

func mustRegexSplit(regex string, s string, n int) ([]string, error) {
	r, err := regexp.Compile(regex)
	if err != nil {
		return []string{}, err
	}
	return r.Split(s, n), nil
}



func base64encode(v string) string {
	return base64.StdEncoding.EncodeToString([]byte(v))
}

func base64decode(v string) string {
	data, err := base64.StdEncoding.DecodeString(v)
	if err != nil {
		return err.Error()
	}
	return string(data)
}

func base32encode(v string) string {
	return base32.StdEncoding.EncodeToString([]byte(v))
}

func base32decode(v string) string {
	data, err := base32.StdEncoding.DecodeString(v)
	if err != nil {
		return err.Error()
	}
	return string(data)
}

func abbrev(width int, s string) string {
	if width < 4 {
		return s
	}
	r, _ := util.Abbreviate(s, width)
	return r
}

func abbrevboth(left, right int, s string) string {
	if right < 4 || left > 0 && right < 7 {
		return s
	}
	r, _ := util.AbbreviateFull(s, left, right)
	return r
}
func initials(s string) string {
	// Wrap this just to eliminate the var args, which templates don't do well.
	return util.Initials(s)
}

func randAlphaNumeric(count int) string {
	// It is not possible, it appears, to actually generate an error here.
	r, _ := util.CryptoRandomAlphaNumeric(count)
	return r
}

func randAlpha(count int) string {
	r, _ := util.CryptoRandomAlphabetic(count)
	return r
}

func randAscii(count int) string {
	r, _ := util.CryptoRandomAscii(count)
	return r
}

func randNumeric(count int) string {
	r, _ := util.CryptoRandomNumeric(count)
	return r
}

func untitle(str string) string {
	return util.Uncapitalize(str)
}

func quote(str ...interface{}) string {
	out := make([]string, 0, len(str))
	for _, s := range str {
		if s != nil {
			out = append(out, fmt.Sprintf("%q", strval(s)))
		}
	}
	return strings.Join(out, " ")
}

func squote(str ...interface{}) string {
	out := make([]string, 0, len(str))
	for _, s := range str {
		if s != nil {
			out = append(out, fmt.Sprintf("'%v'", s))
		}
	}
	return strings.Join(out, " ")
}

func cat(v ...interface{}) string {
	v = removeNilElements(v)
	r := strings.TrimSpace(strings.Repeat("%v ", len(v)))
	return fmt.Sprintf(r, v...)
}

func indent(spaces int, v string) string {
	pad := strings.Repeat(" ", spaces)
	return pad + strings.Replace(v, "\n", "\n"+pad, -1)
}

func nindent(spaces int, v string) string {
	return "\n" + indent(spaces, v)
}

func replace(old, new, src string) string {
	return strings.Replace(src, old, new, -1)
}

func plural(one, many string, count int) string {
	if count == 1 {
		return one
	}
	return many
}

func strslice(v interface{}) []string {
	switch v := v.(type) {
	case []string:
		return v
	case []interface{}:
		b := make([]string, 0, len(v))
		for _, s := range v {
			if s != nil {
				b = append(b, strval(s))
			}
		}
		return b
	default:
		val := reflect.ValueOf(v)
		switch val.Kind() {
		case reflect.Array, reflect.Slice:
			l := val.Len()
			b := make([]string, 0, l)
			for i := 0; i < l; i++ {
				value := val.Index(i).Interface()
				if value != nil {
					b = append(b, strval(value))
				}
			}
			return b
		default:
			if v == nil {
				return []string{}
			}

			return []string{strval(v)}
		}
	}
}

func removeNilElements(v []interface{}) []interface{} {
	newSlice := make([]interface{}, 0, len(v))
	for _, i := range v {
		if i != nil {
			newSlice = append(newSlice, i)
		}
	}
	return newSlice
}

func strval(v interface{}) string {
	switch v := v.(type) {
	case string:
		return v
	case []byte:
		return string(v)
	case error:
		return v.Error()
	case fmt.Stringer:
		return v.String()
	default:
		return fmt.Sprintf("%v", v)
	}
}

func trunc(c int, s string) string {
	if c < 0 && len(s)+c > 0 {
		return s[len(s)+c:]
	}
	if c >= 0 && len(s) > c {
		return s[:c]
	}
	return s
}

func join(sep string, v interface{}) string {
	return strings.Join(strslice(v), sep)
}

func split(sep, orig string) map[string]string {
	parts := strings.Split(orig, sep)
	res := make(map[string]string, len(parts))
	for i, v := range parts {
		res["_"+strconv.Itoa(i)] = v
	}
	return res
}

func splitn(sep string, n int, orig string) map[string]string {
	parts := strings.SplitN(orig, sep, n)
	res := make(map[string]string, len(parts))
	for i, v := range parts {
		res["_"+strconv.Itoa(i)] = v
	}
	return res
}

// substring creates a substring of the given string.
//
// If start is < 0, this calls string[:end].
//
// If start is >= 0 and end < 0 or end bigger than s length, this calls string[start:]
//
// Otherwise, this calls string[start, end].
func substring(start, end int, s string) string {
	if start < 0 {
		return s[:end]
	}
	if end < 0 || end > len(s) {
		return s[start:]
	}
	return s[start:end]
}

func exists(path string) (bool, error) {
	_, err := os.Stat(path)
	if err == nil {
		return true, nil
	}
	if os.IsNotExist(err) {
		return false, nil
	}
	return false, err
}

func getArrayValues(funcName string, entries interface{}) (*reflect.Value, error) {
	entriesVal := reflect.ValueOf(entries)

	kind := entriesVal.Kind()

	if kind == reflect.Ptr {
		entriesVal = reflect.Indirect(entriesVal)
		kind = entriesVal.Kind()
	}

	switch kind {
	case reflect.Array, reflect.Slice:
		break
	default:
		return nil, fmt.Errorf("Must pass an array or slice to '%v'; received %v; kind %v", funcName, entries, kind)
	}
	return &entriesVal, nil
}

// Generalized groupBy function
func generalizedGroupBy(funcName string, entries interface{}, getValue func(interface{}) (interface{}, error), addEntry func(map[string][]interface{}, interface{}, interface{})) (map[string][]interface{}, error) {
	entriesVal, err := getArrayValues(funcName, entries)

	if err != nil {
		return nil, err
	}

	groups := make(map[string][]interface{})
	for i := 0; i < entriesVal.Len(); i++ {
		v := reflect.Indirect(entriesVal.Index(i)).Interface()
		value, err := getValue(v)
		if err != nil {
			return nil, err
		}
		if value != nil {
			addEntry(groups, value, v)
		}
	}
	return groups, nil
}

func generalizedGroupByKey(funcName string, entries interface{}, key string, addEntry func(map[string][]interface{}, interface{}, interface{})) (map[string][]interface{}, error) {
	getKey := func(v interface{}) (interface{}, error) {
		return deepGet(v, key), nil
	}
	return generalizedGroupBy(funcName, entries, getKey, addEntry)
}

func groupByMulti(entries interface{}, key, sep string) (map[string][]interface{}, error) {
	return generalizedGroupByKey("groupByMulti", entries, key, func(groups map[string][]interface{}, value interface{}, v interface{}) {
		items := strings.Split(value.(string), sep)
		for _, item := range items {
			groups[item] = append(groups[item], v)
		}
	})
}

// groupBy groups a generic array or slice by the path property key
func groupBy(entries interface{}, key string) (map[string][]interface{}, error) {
	return generalizedGroupByKey("groupBy", entries, key, func(groups map[string][]interface{}, value interface{}, v interface{}) {
		groups[value.(string)] = append(groups[value.(string)], v)
	})
}

// groupByKeys is the same as groupBy but only returns a list of keys
func groupByKeys(entries interface{}, key string) ([]string, error) {
	keys, err := generalizedGroupByKey("groupByKeys", entries, key, func(groups map[string][]interface{}, value interface{}, v interface{}) {
		groups[value.(string)] = append(groups[value.(string)], v)
	})

	if err != nil {
		return nil, err
	}

	ret := []string{}
	for k := range keys {
		ret = append(ret, k)
	}
	return ret, nil
}

// groupByLabel is the same as groupBy but over a given label
func groupByLabel(entries interface{}, label string) (map[string][]interface{}, error) {
	getLabel := func(v interface{}) (interface{}, error) {
		if container, ok := v.(RuntimeContainer); ok {
			if value, ok := container.Labels[label]; ok {
				return value, nil
			}
			return nil, nil
		}
		return nil, fmt.Errorf("Must pass an array or slice of RuntimeContainer to 'groupByLabel'; received %v", v)
	}
	return generalizedGroupBy("groupByLabel", entries, getLabel, func(groups map[string][]interface{}, value interface{}, v interface{}) {
		groups[value.(string)] = append(groups[value.(string)], v)
	})
}

// Generalized where function
func generalizedWhere(funcName string, entries interface{}, key string, test func(interface{}) bool) (interface{}, error) {
	entriesVal, err := getArrayValues(funcName, entries)

	if err != nil {
		return nil, err
	}

	selection := make([]interface{}, 0)
	for i := 0; i < entriesVal.Len(); i++ {
		v := reflect.Indirect(entriesVal.Index(i)).Interface()

		value := deepGet(v, key)
		if test(value) {
			selection = append(selection, v)
		}
	}

	return selection, nil
}

// selects entries based on key
func where(entries interface{}, key string, cmp interface{}) (interface{}, error) {
	return generalizedWhere("where", entries, key, func(value interface{}) bool {
		return reflect.DeepEqual(value, cmp)
	})
}

// select entries where a key is not equal to a value
func whereNot(entries interface{}, key string, cmp interface{}) (interface{}, error) {
	return generalizedWhere("whereNot", entries, key, func(value interface{}) bool {
		return !reflect.DeepEqual(value, cmp)
	})
}

// selects entries where a key exists
func whereExist(entries interface{}, key string) (interface{}, error) {
	return generalizedWhere("whereExist", entries, key, func(value interface{}) bool {
		return value != nil
	})
}

// selects entries where a key does not exist
func whereNotExist(entries interface{}, key string) (interface{}, error) {
	return generalizedWhere("whereNotExist", entries, key, func(value interface{}) bool {
		return value == nil
	})
}

// selects entries based on key.  Assumes key is delimited and breaks it apart before comparing
func whereAny(entries interface{}, key, sep string, cmp []string) (interface{}, error) {
	return generalizedWhere("whereAny", entries, key, func(value interface{}) bool {
		if value == nil {
			return false
		} else {
			items := strings.Split(value.(string), sep)
			return len(intersect(cmp, items)) > 0
		}
	})
}

// selects entries based on key.  Assumes key is delimited and breaks it apart before comparing
func whereAll(entries interface{}, key, sep string, cmp []string) (interface{}, error) {
	req_count := len(cmp)
	return generalizedWhere("whereAll", entries, key, func(value interface{}) bool {
		if value == nil {
			return false
		} else {
			items := strings.Split(value.(string), sep)
			return len(intersect(cmp, items)) == req_count
		}
	})
}

// generalized whereLabel function
func generalizedWhereLabel(funcName string, containers Context, label string, test func(string, bool) bool) (Context, error) {
	selection := make([]*RuntimeContainer, 0)

	for i := 0; i < len(containers); i++ {
		container := containers[i]

		value, ok := container.Labels[label]
		if test(value, ok) {
			selection = append(selection, container)
		}
	}

	return selection, nil
}

// selects containers that have a particular label
func whereLabelExists(containers Context, label string) (Context, error) {
	return generalizedWhereLabel("whereLabelExists", containers, label, func(_ string, ok bool) bool {
		return ok
	})
}

// selects containers that have don't have a particular label
func whereLabelDoesNotExist(containers Context, label string) (Context, error) {
	return generalizedWhereLabel("whereLabelDoesNotExist", containers, label, func(_ string, ok bool) bool {
		return !ok
	})
}

// selects containers with a particular label whose value matches a regular expression
func whereLabelValueMatches(containers Context, label, pattern string) (Context, error) {
	rx, err := regexp.Compile(pattern)
	if err != nil {
		return nil, err
	}

	return generalizedWhereLabel("whereLabelValueMatches", containers, label, func(value string, ok bool) bool {
		return ok && rx.MatchString(value)
	})
}

// hasPrefix returns whether a given string is a prefix of another string
func hasPrefix(prefix, s string) bool {
	return strings.HasPrefix(s, prefix)
}

// hasSuffix returns whether a given string is a suffix of another string
func hasSuffix(suffix, s string) bool {
	return strings.HasSuffix(s, suffix)
}

func keys(input interface{}) (interface{}, error) {
	if input == nil {
		return nil, nil
	}

	val := reflect.ValueOf(input)
	if val.Kind() != reflect.Map {
		return nil, fmt.Errorf("Cannot call keys on a non-map value: %v", input)
	}

	vk := val.MapKeys()
	k := make([]interface{}, val.Len())
	for i := range k {
		k[i] = vk[i].Interface()
	}

	return k, nil
}

func intersect(l1, l2 []string) []string {
	m := make(map[string]bool)
	m2 := make(map[string]bool)
	for _, v := range l2 {
		m2[v] = true
	}
	for _, v := range l1 {
		if m2[v] {
			m[v] = true
		}
	}
	keys := make([]string, 0, len(m))
	for k := range m {
		keys = append(keys, k)
	}
	return keys
}

func contains(item map[string]string, key string) bool {
	if _, ok := item[key]; ok {
		return true
	}
	return false
}

func dict(values ...interface{}) (map[string]interface{}, error) {
	if len(values)%2 != 0 {
		return nil, errors.New("invalid dict call")
	}
	dict := make(map[string]interface{}, len(values)/2)
	for i := 0; i < len(values); i += 2 {
		key, ok := values[i].(string)
		if !ok {
			return nil, errors.New("dict keys must be strings")
		}
		dict[key] = values[i+1]
	}
	return dict, nil
}

func hashSha1(input string) string {
	h := sha1.New()
	io.WriteString(h, input)
	return fmt.Sprintf("%x", h.Sum(nil))
}

func marshalJson(input interface{}) (string, error) {
	var buf bytes.Buffer
	enc := json.NewEncoder(&buf)
	if err := enc.Encode(input); err != nil {
		return "", err
	}
	return strings.TrimSuffix(buf.String(), "\n"), nil
}

func unmarshalJson(input string) (interface{}, error) {
	var v interface{}
	if err := json.Unmarshal([]byte(input), &v); err != nil {
		return nil, err
	}
	return v, nil
}

// arrayFirst returns first item in the array or nil if the
// input is nil or empty
func arrayFirst(input interface{}) interface{} {
	if input == nil {
		return nil
	}

	arr := reflect.ValueOf(input)

	if arr.Len() == 0 {
		return nil
	}

	return arr.Index(0).Interface()
}

// arrayLast returns last item in the array
func arrayLast(input interface{}) interface{} {
	arr := reflect.ValueOf(input)
	return arr.Index(arr.Len() - 1).Interface()
}

// arrayClosest find the longest matching substring in values
// that matches input
func arrayClosest(values []string, input string) string {
	best := ""
	for _, v := range values {
		if strings.Contains(input, v) && len(v) > len(best) {
			best = v
		}
	}
	return best
}

// dirList returns a list of files in the specified path
func dirList(path string) ([]string, error) {
	names := []string{}
	files, err := ioutil.ReadDir(path)
	if err != nil {
		log.Printf("Template error: %v", err)
		return names, nil
	}
	for _, f := range files {
		names = append(names, f.Name())
	}
	return names, nil
}

// coalesce returns the first non nil argument
func coalesce(input ...interface{}) interface{} {
	for _, v := range input {
		if v != nil {
			return v
		}
	}
	return nil
}

// trimPrefix returns a string without the prefix, if present
func trimPrefix(prefix, s string) string {
	return strings.TrimPrefix(s, prefix)
}

// trimSuffix returns a string without the suffix, if present
func trimSuffix(suffix, s string) string {
	return strings.TrimSuffix(s, suffix)
}

// trim returns the string without leading or trailing whitespace
func trim(s string) string {
	return strings.TrimSpace(s)
}

// when returns the trueValue when the condition is true and the falseValue otherwise
func when(condition bool, trueValue, falseValue interface{}) interface{} {
	if condition {
		return trueValue
	} else {
		return falseValue
	}
}


func newTemplate(name string) *template.Template {
	tmpl := template.New(name).Funcs(template.FuncMap{
		"closest":                arrayClosest,
		"coalesce":               coalesce,
		"contains":               contains,
		"dict":                   dict,
		"dir":                    dirList,
		"exists":                 exists,
		"first":                  arrayFirst,
		"groupBy":                groupBy,
		"groupByKeys":            groupByKeys,
		"groupByMulti":           groupByMulti,
		"groupByLabel":           groupByLabel,
		"hasPrefix":              hasPrefix,
		"hasSuffix":              hasSuffix,
		"json":                   marshalJson,
		"intersect":              intersect,
		"keys":                   keys,
		"last":                   arrayLast,
		"replace":                strings.Replace,
		"parseBool":              strconv.ParseBool,
		"parseJson":              unmarshalJson,
		"queryEscape":            url.QueryEscape,
		"sha1":                   hashSha1,
		"split":                  strings.Split,
		"splitN":                 strings.SplitN,
		"trimPrefix":             trimPrefix,
		"trimSuffix":             trimSuffix,
		"trim":                   trim,
		"when":                   when,
		"where":                  where,
		"whereNot":               whereNot,
		"whereExist":             whereExist,
		"whereNotExist":          whereNotExist,
		"whereAny":               whereAny,
		"whereAll":               whereAll,
		"whereLabelExists":       whereLabelExists,
		"whereLabelDoesNotExist": whereLabelDoesNotExist,
		"whereLabelValueMatches": whereLabelValueMatches,
		"regexMatch":             regexMatch,
		"mustRegexMatch":         mustRegexMatch,
		"regexFindAll":           regexFindAll,
		"mustRegexFindAll":       mustRegexFindAll,
		"regexFind":              regexFind,
		"mustRegexFind" : mustRegexFind ,
		"regexReplaceAll" :  regexReplaceAll,
		"mustRegexReplaceAll" :  mustRegexReplaceAll,
		"regexReplaceAllLiteral" :  regexReplaceAllLiteral,
		"mustRegexReplaceAllLiteral" :  mustRegexReplaceAllLiteral,
		"regexSplit" :  regexSplit,
		"mustRegexSplit" :  mustRegexSplit,
		"base64encode" : base64encode,
		"base64decode" : base64decode,
		"base32encode" : base32encode,
		"base32decode" : base32decode,
		"abbrev" :  abbrev,
		"abbrevboth" : abbrevboth,
		"initials" :  initials,
		"randAlphaNumeric" :  randAlphaNumeric,
		"randAlpha" : randAlpha,
		"randAscii" :  randAscii,
		"randNumeric" : randNumeric,
		"untitle" : untitle,
		"quote" :  quote,
		"squote" :  squote,
		"cat" :  cat,
		"indent" :  indent,
		"nindent" :  nindent,
		"plural" : plural,
		"strslice" : strslice,
		"removeNilElements" :  removeNilElements,
		"strval" : strval,
		"trunc" :  trunc,
		"join" : join,
		"splitn" :  splitn,
		"substring" :  substring,
		"getenv" : os.Getenv,
		"environment" : environment,
		"readEnv" : readEnv,

	})
	//	"replace" :  replace,
	//	"split" : split,
	return tmpl
}

func filterRunning(config Config, containers Context) Context {
	if config.IncludeStopped {
		return containers
	} else {
		filteredContainers := Context{}
		for _, container := range containers {
			if container.State.Running {
				filteredContainers = append(filteredContainers, container)
			}
		}
		return filteredContainers
	}
}

func GenerateFile(config Config, containers Context) bool {
	filteredRunningContainers := filterRunning(config, containers)
	filteredContainers := Context{}
	if config.OnlyPublished {
		for _, container := range filteredRunningContainers {
			if len(container.PublishedAddresses()) > 0 {
				filteredContainers = append(filteredContainers, container)
			}
		}
	} else if config.OnlyExposed {
		for _, container := range filteredRunningContainers {
			if len(container.Addresses) > 0 {
				filteredContainers = append(filteredContainers, container)
			}
		}
	} else {
		filteredContainers = filteredRunningContainers
	}

	contents := executeTemplate(config.Template, filteredContainers)

	if !config.KeepBlankLines {
		buf := new(bytes.Buffer)
		removeBlankLines(bytes.NewReader(contents), buf)
		contents = buf.Bytes()
	}

	if config.Dest != "" {
		dest, err := ioutil.TempFile(filepath.Dir(config.Dest), "docker-gen")
		defer func() {
			dest.Close()
			os.Remove(dest.Name())
		}()
		if err != nil {
			log.Fatalf("Unable to create temp file: %s\n", err)
		}

		if n, err := dest.Write(contents); n != len(contents) || err != nil {
			log.Fatalf("Failed to write to temp file: wrote %d, exp %d, err=%v", n, len(contents), err)
		}

		oldContents := []byte{}
		if fi, err := os.Stat(config.Dest); err == nil {
			if err := dest.Chmod(fi.Mode()); err != nil {
				log.Fatalf("Unable to chmod temp file: %s\n", err)
			}
			if err := dest.Chown(int(fi.Sys().(*syscall.Stat_t).Uid), int(fi.Sys().(*syscall.Stat_t).Gid)); err != nil {
				log.Fatalf("Unable to chown temp file: %s\n", err)
			}
			oldContents, err = ioutil.ReadFile(config.Dest)
			if err != nil {
				log.Fatalf("Unable to compare current file contents: %s: %s\n", config.Dest, err)
			}
		}

		if bytes.Compare(oldContents, contents) != 0 {
			err = os.Rename(dest.Name(), config.Dest)
			if err != nil {
				log.Fatalf("Unable to create dest file %s: %s\n", config.Dest, err)
			}
			log.Printf("Generated '%s' from %d containers", config.Dest, len(filteredContainers))
			return true
		}
		return false
	} else {
		os.Stdout.Write(contents)
	}
	return true
}

func executeTemplate(templatePath string, containers Context) []byte {
	tmpl, err := newTemplate(filepath.Base(templatePath)).ParseFiles(templatePath)
	if err != nil {
		log.Fatalf("Unable to parse template: %s", err)
	}

	buf := new(bytes.Buffer)
	err = tmpl.ExecuteTemplate(buf, filepath.Base(templatePath), &containers)
	if err != nil {
		log.Fatalf("Template error: %s\n", err)
	}
	return buf.Bytes()
}
