// Hygienic syntax-rules macro support for the little Scheme interpreter.
//
// The expander implements the explicit-renaming (ER) hygiene model on top of
// the existing tree-walking evaluator:
//
//   - Scheme source is converted, before evaluation, into "syntax" in which
//     identifiers are *sid values carrying a name plus at most one rename tag.
//   - On each macro invocation every identifier that occurs freely in the
//     rule template (i.e. introduced by the macro) is stamped with a fresh
//     tag linked to the compile-time environment of the transformer's
//     definition site.  Identifiers substituted from the macro input keep
//     their own identity, so caller bindings and macro-introduced bindings
//     can never capture each other.
//   - Resolution of a tagged identifier first tries an exact name+tag match
//     in the use-site environment (so a macro-introduced binder and its
//     references agree) and, failing that, resolves the bare name in the
//     tag's definition-site environment (so free template identifiers keep
//     their definition-site binding location, observable by later set!).
//   - Expansion yields ordinary datum made of the original interned symbols
//     (globals) and fresh uninterned symbols (lexical binders); quoted data
//     always consists of plain interned symbols.
package main

import (
	"fmt"

	"github.com/nukata/goarith"
)

var ellipsisSym = Intern("...")
var underscoreSym = Intern("_")
var syntaxRulesSym = Intern("syntax-rules")
var defineSyntaxSym = Intern("define-syntax")
var letSyntaxSym = Intern("let-syntax")
var letrecSyntaxSym = Intern("letrec-syntax")

//----------------------------------------------------------------------
// Syntax identifiers
//----------------------------------------------------------------------

// A tag links a macro-introduced identifier to the compile-time environment
// of the transformer invocation that introduced it.
type renameTag struct {
	id int
	ce *ctFrame
}

var tagCounter int

func newTag(ce *ctFrame) *renameTag {
	tagCounter++
	return &renameTag{tagCounter, ce}
}

// sid is an identifier during macro expansion: a printed name plus at most one
// rename tag (nil means an identifier originating from user source).
type sid struct {
	name *Symbol
	tag  *renameTag
}

func sameTag(a, b *renameTag) bool {
	return a == b // pointer identity; tags are unique
}

// boundEq reports whether two identifiers have the same binding identity.
func boundEq(a, b *sid) bool {
	return *a.name == *b.name && sameTag(a.tag, b.tag)
}

// toSyntax converts reader datum to syntax, structurally copying pairs and
// replacing each *Symbol with an untagged *sid.
func toSyntax(x Any) Any {
	switch z := x.(type) {
	case *Symbol:
		return &sid{name: z}
	case *Cell:
		return syntaxCell(z)
	default:
		return x
	}
}

func syntaxCell(j *Cell) Any {
	if j == Nil {
		return Nil
	}
	return &Cell{toSyntax(j.Car), syntaxCdr(j.Cdr)}
}

func syntaxCdr(x Any) Any {
	if j, ok := x.(*Cell); ok {
		if j == Nil {
			return Nil
		}
		return &Cell{toSyntax(j.Car), syntaxCdr(j.Cdr)}
	}
	return toSyntax(x)
}

// datafy converts syntax back to plain datum.  Identifiers collapse to their
// printed (interned) name, so quoted data never exposes generated identity.
func datafy(x Any) Any {
	switch z := x.(type) {
	case *sid:
		return z.name
	case *Cell:
		if z == Nil {
			return Nil
		}
		return &Cell{datafy(z.Car), datafyCdr(z.Cdr)}
	default:
		return x
	}
}

func datafyCdr(x Any) Any {
	if j, ok := x.(*Cell); ok {
		if j == Nil {
			return Nil
		}
		return &Cell{datafy(j.Car), datafyCdr(j.Cdr)}
	}
	return datafy(x)
}

//----------------------------------------------------------------------
// Compile-time environments
//----------------------------------------------------------------------

const (
	bindVar   = iota // a lexical variable, key v
	bindMacro        // a local macro, key mac
)

// ctFrame is one frame of the compile-time environment.
type ctFrame struct {
	name *Symbol
	tag  *renameTag
	kind int
	v    *Symbol // bindVar: runtime key (fresh or interned)
	mac  *transformer
	next *ctFrame
}

// lookupExact finds a frame matching the identifier's name and tag exactly.
func (ce *ctFrame) lookupExact(s *sid) *ctFrame {
	for ce != nil {
		if *ce.name == *s.name && sameTag(ce.tag, s.tag) {
			return ce
		}
		ce = ce.next
	}
	return nil
}

// lookupName finds the nearest frame with the given name regardless of tag;
// used only to follow an identifier's definition-site lexical environment.
func (ce *ctFrame) lookupName(name *Symbol) *ctFrame {
	for ce != nil {
		if *ce.name == *name {
			return ce
		}
		ce = ce.next
	}
	return nil
}

// resolveID resolves a syntax identifier to its binding frame:
// first exact use-site identity, then its tag's definition-site environment.
func resolveID(s *sid, ce *ctFrame) *ctFrame {
	if f := ce.lookupExact(s); f != nil {
		return f
	}
	if s.tag != nil {
		if f := s.tag.ce.lookupName(s.name); f != nil {
			return f
		}
	}
	return nil
}

// bindingLocation returns a comparable token for the lexical binding of an
// identifier: a runtime *Symbol for variables and globals, a *transformer
// for a macro binding, or an interned name for a free global identifier.
func bindingLocation(s *sid, ce *ctFrame) Any {
	f := resolveID(s, ce)
	if f == nil {
		return s.name
	}
	if f.kind == bindVar {
		return f.v
	}
	return f.mac
}

// freeEq implements free-identifier=?: equality of the resolved lexical
// binding locations (an unbound identifier resolves to its global name).
func freeEq(a, b *sid, ca, cb *ctFrame) bool {
	return bindingLocation(a, ca) == bindingLocation(b, cb)
}

// globalMacros holds macros defined at the top level; they survive across
// REPL inputs and script top-level forms.
var globalMacros = map[*Symbol]*transformer{}

// topCE builds the outermost compile-time frame chain from globalMacros.
func topCE() *ctFrame {
	var ce *ctFrame
	for sym, t := range globalMacros {
		ce = &ctFrame{name: sym, kind: bindMacro, mac: t, next: ce}
	}
	return ce
}

var gensymCounter int

// gensym makes a fresh uninterned runtime key; it keeps the original printed
// text so debug representations of closures stay unchanged.
func gensym(name *Symbol) *Symbol {
	gensymCounter++
	s := Symbol(string(*name))
	return &s
}

//----------------------------------------------------------------------
// Transformers
//----------------------------------------------------------------------

type rule struct {
	pat   Any
	tmpl  Any
	pvars map[*Symbol]int // pattern variable name -> ellipsis depth
}

type transformer struct {
	ce    *ctFrame         // definition-site compile-time environment
	lits  map[*Symbol]*sid // literal identifiers (untagged, at definition)
	rules []*rule
}

// compileTransformer builds a transformer from a (syntax-rules ...) form.
func compileTransformer(spec Any, ce *ctFrame) *transformer {
	z, ok := spec.(*Cell)
	if !ok || z == Nil {
		panic(fmt.Errorf("ill-formed macro transformer: %s",
			Stringify(datafy(spec), true)))
	}
	h, ok := z.Car.(*sid)
	if !ok || h.name != syntaxRulesSym {
		panic(fmt.Errorf("only syntax-rules transformers are supported: %s",
			Stringify(datafy(spec), true)))
	}
	r := z.Cdr.(*Cell)
	litCell, ok := r.Car.(*Cell)
	if !ok {
		panic(fmt.Errorf("syntax-rules requires a list of literals"))
	}
	lits := map[*Symbol]*sid{}
	for j := litCell; j != Nil; j = j.Cdr.(*Cell) {
		s, ok := j.Car.(*sid)
		if !ok {
			panic(fmt.Errorf("syntax-rules literal must be an identifier: %s",
				Stringify(datafy(j.Car), true)))
		}
		lits[s.name] = s
	}
	t := &transformer{ce: ce, lits: lits}
	for j := r.Cdr.(*Cell); j != Nil; j = j.Cdr.(*Cell) {
		rc, ok := j.Car.(*Cell)
		if !ok || rc == Nil {
			panic(fmt.Errorf("syntax-rules clause must be (pattern template)"))
		}
		q := rc.Cdr.(*Cell)
		if q == Nil || q.Cdr != Nil {
			panic(fmt.Errorf("syntax-rules clause must be (pattern template)"))
		}
		pat := rc.Car
		tmpl := q.Car
		validatePattern(pat, true)
		validateTemplate(tmpl)
		pvars := map[*Symbol]int{}
		collectPatternVars(pat, 0, lits, pvars, true)
		t.rules = append(t.rules, &rule{pat, tmpl, pvars})
	}
	if len(t.rules) == 0 {
		panic(fmt.Errorf("syntax-rules requires at least one clause"))
	}
	return t
}

// validatePattern rejects malformed patterns at definition time.
func validatePattern(p Any, atHead bool) {
	switch z := p.(type) {
	case *sid:
		if z.name == ellipsisSym {
			panic(fmt.Errorf("misplaced '...' in pattern"))
		}
	case *Cell:
		if z == Nil {
			if atHead {
				panic(fmt.Errorf("empty macro pattern"))
			}
			return
		}
		validatePattern(z.Car, false)
		validatePatternTail(z.Cdr)
	default:
		// constants are fine as pattern elements
	}
}

func validatePatternTail(q Any) {
	if q == Nil {
		return
	}
	if j, ok := q.(*Cell); ok {
		if j != Nil {
			if e, isID := j.Car.(*sid); isID && e.name == ellipsisSym {
				if _, isCell := j.Cdr.(*Cell); !isCell {
					panic(fmt.Errorf("'...' must follow a subpattern"))
				}
				rest := j.Cdr
				for {
					if c, isCell := rest.(*Cell); isCell && c != Nil {
						if e2, isID2 := c.Car.(*sid); isID2 &&
							e2.name == ellipsisSym {
							rest = c.Cdr
							continue
						}
					}
					break
				}
				validatePatternTail(rest)
				return
			}
			validatePattern(j.Car, false)
			validatePatternTail(j.Cdr)
		}
		return
	}
	validatePattern(q, false) // dotted atom
}

// collectPatternVars records each pattern variable's ellipsis depth.
// head is true only for the top-level pattern, whose first element is the
// macro keyword.
func collectPatternVars(p Any, d int, lits map[*Symbol]*sid,
	set map[*Symbol]int, head bool) {
	switch z := p.(type) {
	case *sid:
		if z.name == ellipsisSym || z.name == underscoreSym {
			return
		}
		if _, isLit := lits[z.name]; isLit {
			return
		}
		if old, ok := set[z.name]; ok && old != d {
			panic(fmt.Errorf(
				"pattern variable %s used at differing ellipsis depths", *z.name))
		}
		set[z.name] = d
	case *Cell:
		if z == Nil {
			return
		}
		patVarsChain(z, d, lits, set, head)
	}
}

// patVarsChain walks a pattern chain; the first element may be the keyword.
func patVarsChain(j *Cell, d int, lits map[*Symbol]*sid, set map[*Symbol]int,
	head bool) {
	if j == Nil {
		return
	}
	if q, ok := j.Cdr.(*Cell); ok && q != Nil {
		if e, isID := q.Car.(*sid); isID && e.name == ellipsisSym {
			// Consecutive ellipses (x ... ...) each add one repetition level.
			depth := d + 1
			rest := q.Cdr
			for {
				if c, isCell := rest.(*Cell); isCell && c != Nil {
					if e2, isID2 := c.Car.(*sid); isID2 &&
						e2.name == ellipsisSym {
						depth++
						rest = c.Cdr
						continue
					}
				}
				break
			}
			collectPatternVars(j.Car, depth, lits, set, false)
			patVarsRest(rest, d, lits, set)
			return
		}
	}
	if !head {
		collectPatternVars(j.Car, d, lits, set, false)
	}
	patVarsRest(j.Cdr, d, lits, set)
}

func patVarsRest(q Any, d int, lits map[*Symbol]*sid, set map[*Symbol]int) {
	if j, ok := q.(*Cell); ok {
		patVarsChain(j, d, lits, set, false)
	} else {
		collectPatternVars(q, d, lits, set, false)
	}
}

// validateTemplate rejects stray ellipses in templates at definition time.
func validateTemplate(t Any) {
	switch z := t.(type) {
	case *sid:
		if z.name == ellipsisSym {
			panic(fmt.Errorf("misplaced '...' in template"))
		}
	case *Cell:
		if z == Nil {
			return
		}
		validateTemplate(z.Car)
		validateTemplateTail(z.Cdr)
	default:
	}
}

func validateTemplateTail(q Any) {
	if q == Nil {
		return
	}
	if j, ok := q.(*Cell); ok {
		if j != Nil {
			if e, isID := j.Car.(*sid); isID && e.name == ellipsisSym {
				if _, isCell := j.Cdr.(*Cell); !isCell {
					panic(fmt.Errorf("'...' must follow a template element"))
				}
				rest := j.Cdr
				for {
					if c, isCell := rest.(*Cell); isCell && c != Nil {
						if e2, isID2 := c.Car.(*sid); isID2 &&
							e2.name == ellipsisSym {
							rest = c.Cdr
							continue
						}
					}
					break
				}
				validateTemplateTail(rest)
				return
			}
			validateTemplate(j.Car)
			validateTemplateTail(j.Cdr)
		}
		return
	}
	validateTemplate(q)
}

//----------------------------------------------------------------------
// Pattern matching
//----------------------------------------------------------------------

type cap struct {
	depth int // number of enclosing ellipses in the pattern
	v     Any // scalar at depth 0, []Any at depth 1, nested further
}

type matcher struct {
	t     *transformer
	useCE *ctFrame
	b     map[*Symbol]*cap
}

// apply tries the rules in declaration order; it never evaluates anything.
func (t *transformer) apply(form *Cell, useCE *ctFrame) Any {
	ih, headIsID := form.Car.(*sid)
	for _, r := range t.rules {
		pc := r.pat.(*Cell) // checked by validatePattern
		ph := pc.Car.(*sid)
		headOK := false
		if ph.name == underscoreSym {
			headOK = true
		} else if headIsID {
			headOK = freeEq(ph, ih, t.ce, useCE)
			if !headOK {
				// The pattern may literally name this transformer's keyword.
				if loc, ok := bindingLocation(ph, t.ce).(*transformer); ok && loc == t {
					headOK = true
				}
			}
		}
		if !headOK {
			continue
		}
		m := &matcher{t: t, useCE: useCE, b: map[*Symbol]*cap{}}
		if m.matchCells(pc.Cdr, form.Cdr, 0) {
			return t.gen(r.tmpl, m.b, r.pvars)
		}
	}
	panic(fmt.Errorf("no syntax-rule matched: %s", Stringify(datafy(form), true)))
}

// matchCells matches a pattern chain against an input chain.
// Returns false for ordinary mismatch; panics only for malformed patterns.
func (m *matcher) matchCells(pc, xc Any, d int) bool {
	if pc == Nil {
		return xc == Nil
	}
	ppc, patIsCell := pc.(*Cell)
	if !patIsCell {
		return m.matchOne(pc, xc, d)
	}
	xcc, inIsCell := xc.(*Cell)
	if !inIsCell {
		return false
	}
	p := ppc.Car
	if q, ok := ppc.Cdr.(*Cell); ok && q != Nil {
		if e, isID := q.Car.(*sid); isID && e.name == ellipsisSym {
			return m.matchEllipsis(p, q.Cdr, xcc, d)
		}
	}
	if !m.matchOne(p, xcc.Car, d) {
		return false
	}
	return m.matchCells(ppc.Cdr, xcc.Cdr, d)
}

func (m *matcher) matchOne(p, x Any, d int) bool {
	switch pp := p.(type) {
	case *sid:
		if pp.name == ellipsisSym {
			panic(fmt.Errorf("misplaced '...' in pattern"))
		}
		if pp.name == underscoreSym {
			return true
		}
		if lit, isLit := m.t.lits[pp.name]; isLit {
			xi, ok := x.(*sid)
			return ok && freeEq(lit, xi, m.t.ce, m.useCE)
		}
		// pattern variable
		if old := m.b[pp.name]; old != nil {
			if old.depth != d {
				panic(fmt.Errorf("pattern variable %s used at differing ellipsis depths",
					*pp.name))
			}
			return syntaxEq(old.v, x)
		}
		m.b[pp.name] = &cap{d, x}
		return true
	case *Cell:
		xc, ok := x.(*Cell)
		if !ok {
			return false
		}
		return m.matchCells(pp, xc, d)
	default:
		return syntaxEq(pp, x)
	}
}

// matchEllipsis handles (P ... . rest): repetitions of P, then rest.
// It tries the longest repetition first and backtracks over the split point.
func (m *matcher) matchEllipsis(P, rest Any, xc *Cell, d int) bool {
	// Additional chained markers (P ... ...) do not consume input.
	realRest := rest
	for {
		if c, ok := realRest.(*Cell); ok && c != Nil {
			if e, isID := c.Car.(*sid); isID && e.name == ellipsisSym {
				realRest = c.Cdr
				continue
			}
		}
		break
	}
	n := 0
	proper := true
	j := Any(xc)
	for {
		c, ok := j.(*Cell)
		if !ok {
			proper = false
			break
		}
		if c == Nil {
			break
		}
		n++
		j = c.Cdr
	}
	base := m.b
	maxK := n
	for k := maxK; k >= 0; k-- {
		att := copyCaps(base)
		ok := true
		el := xc
		for i := 0; i < k; i++ {
			child := map[*Symbol]*cap{}
			saved := m.b
			m.b = child
			matched := m.matchOne(P, el.Car, d+1)
			childResult := m.b // nested ellipses replace the map itself
			m.b = saved
			if !matched {
				ok = false
				break
			}
			mergeChild(att, childResult)
			cell, isCell := el.Cdr.(*Cell)
			if !isCell {
				ok = false
				break
			}
			el = cell
		}
		if ok {
			saved := m.b
			m.b = att
			matched := m.matchCells(realRest, el, d)
			m.b = saved
			if matched {
				m.b = att
				return true
			}
		}
	}
	if realRest == Nil && !proper {
		return false
	}
	return false
}

func copyCaps(b map[*Symbol]*cap) map[*Symbol]*cap {
	c := make(map[*Symbol]*cap, len(b))
	for k, v := range b {
		c[k] = v
	}
	return c
}

// mergeChild folds one repetition iteration's captures into the accumulator.
func mergeChild(att, child map[*Symbol]*cap) {
	for nm, c := range child {
		old := att[nm]
		if old == nil {
			att[nm] = &cap{c.depth, []Any{c.v}}
		} else {
			if old.depth != c.depth {
				panic(fmt.Errorf("ellipsis depth mismatch for pattern variable %s",
					*nm))
			}
			old.v = append(old.v.([]Any), c.v)
		}
	}
}

// syntaxEq compares syntax datums: identifiers by binding identity,
// numbers numerically, other constants normally.
func syntaxEq(a, b Any) bool {
	ai, aok := a.(*sid)
	bi, bok := b.(*sid)
	if aok || bok {
		if !aok || !bok {
			return false
		}
		return boundEq(ai, bi)
	}
	ac, aok2 := a.(*Cell)
	bc, bok2 := b.(*Cell)
	if aok2 || bok2 {
		if !aok2 || !bok2 {
			return false
		}
		if ac == Nil || bc == Nil {
			return ac == bc
		}
		return syntaxEq(ac.Car, bc.Car) && syntaxEq(ac.Cdr, bc.Cdr)
	}
	if na, nb := goarith.AsNumber(a), goarith.AsNumber(b); na != nil && nb != nil {
		return na.Cmp(nb) == 0
	}
	return a == b
}

//----------------------------------------------------------------------
// Template instantiation
//----------------------------------------------------------------------

func (t *transformer) gen(tmpl Any, b map[*Symbol]*cap,
	pvars map[*Symbol]int) Any {
	tg := newTag(t.ce)
	return t.genD(tmpl, 0, b, pvars, tg)
}

// genD instantiates a template at ellipsis depth d.
func (t *transformer) genD(tmpl Any, d int, b map[*Symbol]*cap,
	pvars map[*Symbol]int, tg *renameTag) Any {
	switch z := tmpl.(type) {
	case *sid:
		if z.name == ellipsisSym {
			panic(fmt.Errorf("misplaced '...' in template"))
		}
		if _, isVar := pvars[z.name]; isVar {
			c, ok := b[z.name]
			if !ok || c.depth != d {
				cd := -1
				if ok {
					cd = c.depth
				}
				panic(fmt.Errorf(
					"pattern variable %s has mismatched ellipsis level in template (got depth %d, want %d)",
					*z.name, cd, d))
			}
			return c.v // caller-origin syntax keeps its own identity
		}
		return &sid{name: z.name, tag: tg} // macro-introduced identifier
	case *Cell:
		if z == Nil {
			return Nil
		}
		if q, ok := z.Cdr.(*Cell); ok && q != Nil {
			if e, isID := q.Car.(*sid); isID && e.name == ellipsisSym {
				k, rest := countEllipses(q)
				return t.genMarked(z.Car, k, rest, d, b, pvars, tg)
			}
		}
		return &Cell{t.genD(z.Car, d, b, pvars, tg),
			t.genTail(z.Cdr, d, b, pvars, tg)}
	default:
		return tmpl
	}
}

func (t *transformer) genTail(q Any, d int, b map[*Symbol]*cap,
	pvars map[*Symbol]int, tg *renameTag) Any {
	if j, ok := q.(*Cell); ok {
		if j == Nil {
			return Nil
		}
		if q2, ok := j.Cdr.(*Cell); ok && q2 != Nil {
			if e, isID := q2.Car.(*sid); isID && e.name == ellipsisSym {
				k, rest := countEllipses(q2)
				return t.genMarked(j.Car, k, rest, d, b, pvars, tg)
			}
		}
		return &Cell{t.genD(j.Car, d, b, pvars, tg),
			t.genTail(j.Cdr, d, b, pvars, tg)}
	}
	return t.genD(q, d, b, pvars, tg)
}

// countEllipses counts consecutive ellipsis markers following an element.
func countEllipses(q *Cell) (int, Any) {
	k := 1
	r := q.Cdr
	for {
		if c, ok := r.(*Cell); ok && c != Nil {
			if e, isID := c.Car.(*sid); isID && e.name == ellipsisSym {
				k++
				r = c.Cdr
				continue
			}
		}
		break
	}
	return k, r
}

// genMarked builds (P <k ellipses> . rest).  k==1 repeats P once per outer
// match; k>1 flattens additional levels (x ... ... splices nested rows).
// Variables of the rule with depth > d supply the outer repetition count and
// all such counts must agree.  A variable absent from b matched zero times.
func (t *transformer) genMarked(P Any, k int, rest Any, d int,
	b map[*Symbol]*cap, pvars map[*Symbol]int, tg *renameTag) Any {
	names := map[*Symbol]bool{}
	collectVars(P, pvars, names)
	n := -1
	for nm := range names {
		if pvars[nm] > d {
			length := 0
			if c, ok := b[nm]; ok {
				row, isRow := c.v.([]Any)
				if !isRow {
					panic(fmt.Errorf("bad repetition for pattern variable %s",
						*nm))
				}
				length = len(row)
			}
			if n < 0 {
				n = length
			} else if n != length {
				panic(fmt.Errorf(
					"ellipsis repetition lengths do not match (%s gives %d, want %d)",
					*nm, length, n))
			}
		}
	}
	if n < 0 {
		panic(fmt.Errorf("template repetition '...' has no repeating variable"))
	}
	var head []Any
	for i := 0; i < n; i++ {
		b2 := copyCaps(b)
		for nm := range names {
			if pvars[nm] > d {
				if c, ok := b[nm]; ok {
					row := c.v.([]Any)
					b2[nm] = &cap{c.depth - 1, row[i]}
				}
			}
		}
		if k == 1 {
			head = append(head, t.genD(P, d, b2, pvars, tg))
		} else {
			sub := t.genMarked(P, k-1, Nil, d, b2, pvars, tg).(*Cell)
			for j := sub; j != Nil; j = j.Cdr.(*Cell) {
				head = append(head, j.Car)
			}
		}
	}
	tail := t.genTail(rest, d, b, pvars, tg)
	return splice(head, tail)
}

// collectVars collects names of pattern variables of the rule occurring in a
// template element.
func collectVars(x Any, pvars map[*Symbol]int, set map[*Symbol]bool) {
	switch z := x.(type) {
	case *sid:
		if _, ok := pvars[z.name]; ok {
			set[z.name] = true
		}
	case *Cell:
		if z == Nil {
			return
		}
		collectVars(z.Car, pvars, set)
		collectVarsCdr(z.Cdr, pvars, set)
	}
}

func collectVarsCdr(q Any, pvars map[*Symbol]int, set map[*Symbol]bool) {
	if j, ok := q.(*Cell); ok {
		if j == Nil {
			return
		}
		collectVars(j.Car, pvars, set)
		collectVarsCdr(j.Cdr, pvars, set)
		return
	}
	collectVars(q, pvars, set)
}

func splice(head []Any, tail Any) Any {
	if len(head) == 0 {
		if tail == Nil {
			return Nil
		}
		if c, ok := tail.(*Cell); ok {
			return c
		}
		// Improper zero-length repetition ending in a non-nil atom would be
		// malformed; leave as a dotted pair chain ending at the atom.
		return tail
	}
	result := &Cell{head[len(head)-1], tail}
	for i := len(head) - 2; i >= 0; i-- {
		result = &Cell{head[i], result}
	}
	return result
}

//----------------------------------------------------------------------
// Expansion
//----------------------------------------------------------------------

// ExpandTopLevel fully expands a top-level reader datum into evaluable datum.
func ExpandTopLevel(exp Any) Any {
	macroDepth = 0
	out, _ := expandSeq(toCellList(toSyntax(exp)), topCE(), true, false)
	return out
}

// toCellList ensures a single form is treated as a one-element list of forms.
func toCellList(x Any) *Cell {
	return &Cell{x, Nil}
}

// expandSeq expands a sequence (a lambda/let-syntax body, a begin, or the
// top level), threading define and define-syntax bindings into the
// compile-time environment for later forms.  An isBody sequence pre-binds
// body-level definitions (descending through nested begins, letrec* style)
// so that lambdas in a definition's right-hand side can refer recursively
// to the defined name and so that definitions inside nested begins share
// the same frame slot as references after the begin, matching the
// interpreter's frame-top internal defines.
func expandSeq(forms *Cell, ce *ctFrame, top, isBody bool) (Any, *ctFrame) {
	if !top && isBody {
		ce = preBindBodyDefines(forms, ce)
	}
	out := make([]Any, 0, 4)
	for forms != Nil {
		e := forms.Car
		forms = forms.Cdr.(*Cell)
		if z, ok := e.(*Cell); ok && z != Nil {
			if h, ok := z.Car.(*sid); ok {
				switch h.name {
				case defineSym:
					em, ce2 := expandDefine(z, ce, top)
					ce = ce2
					out = append(out, em)
					continue
				case defineSyntaxSym:
					ce = expandDefineSyntax(z, ce, top)
					out = append(out, Void)
					continue
				}
			}
		}
		out = append(out, expandExpr(e, ce, top))
	}
	switch len(out) {
	case 0:
		panic(fmt.Errorf("empty body"))
	case 1:
		return out[0], ce
	default:
		items := make([]Any, 0, len(out)+1)
		items = append(items, beginSym)
		items = append(items, out...)
		return listFrom(items...), ce
	}
}

// preBindBodyDefines reserves compile-time frames for all body-level define
// and define-syntax forms (descending into nested begins, which are
// transparent to frame-top definitions), in reverse textual order (the last
// definition is nearest, as with the evaluator's frame-top semantics).
func preBindBodyDefines(forms *Cell, ce *ctFrame) *ctFrame {
	var defs []*Cell
	var collect func(Any)
	collect = func(e Any) {
		z, ok := e.(*Cell)
		if !ok || z == Nil {
			return
		}
		h, ok := z.Car.(*sid)
		if !ok {
			return
		}
		switch h.name {
		case defineSym, defineSyntaxSym:
			defs = append(defs, z)
		case beginSym:
			for j := z.Cdr.(*Cell); j != Nil; j = j.Cdr.(*Cell) {
				collect(j.Car)
			}
		}
	}
	for j := forms; j != Nil; j = j.Cdr.(*Cell) {
		collect(j.Car)
	}
	for i := len(defs) - 1; i >= 0; i-- {
		z := defs[i]
		h := z.Car.(*sid)
		q := z.Cdr.(*Cell)
		s, ok := q.Car.(*sid)
		if !ok {
			continue
		}
		if h.name == defineSym {
			ce = &ctFrame{name: s.name, tag: s.tag, kind: bindVar,
				v: gensym(s.name), next: ce}
		} else {
			ce = &ctFrame{name: s.name, tag: s.tag, kind: bindMacro, next: ce}
		}
	}
	return ce
}

func expandExpr(x Any, ce *ctFrame, top bool) Any {
	switch z := x.(type) {
	case *sid:
		f := resolveID(z, ce)
		if f == nil {
			return z.name // global variable
		}
		if f.kind == bindVar {
			return f.v
		}
		panic(fmt.Errorf("syntax keyword %s used as an expression", *z.name))
	case *Cell:
		if z == Nil {
			return Nil
		}
		return expandForm(z, ce, top)
	default:
		return x
	}
}

func expandForm(z *Cell, ce *ctFrame, top bool) Any {
	h, headIsID := z.Car.(*sid)
	if headIsID {
		switch h.name {
		case quoteSym:
			d, ok := z.Cdr.(*Cell)
			if !ok || d == Nil || d.Cdr != Nil {
				panic(fmt.Errorf("malformed quote"))
			}
			return &Cell{quoteSym, &Cell{datafy(d.Car), Nil}}
		case ifSym:
			return expandIf(z, ce, top)
		case beginSym:
			out, _ := expandSeq(z.Cdr.(*Cell), ce, top, false)
			return out
		case lambdaSym:
			return expandLambda(z, ce, top)
		case defineSym:
			out, _ := expandDefine(z, ce, top)
			return out
		case setQSym:
			return expandSetQ(z, ce, top)
		case defineSyntaxSym:
			expandDefineSyntax(z, ce, top)
			return Void
		case letSyntaxSym, letrecSyntaxSym:
			return expandLetSyntax(z, ce, top, h.name == letrecSyntaxSym)
		case syntaxRulesSym:
			panic(fmt.Errorf("syntax-rules is only valid as a macro transformer"))
		}
		// A macro binding visible at the use site or at the identifier's
		// definition site (through its rename tag).
		if f := resolveID(h, ce); f != nil {
			if f.kind == bindMacro {
				if f.mac == nil {
					panic(fmt.Errorf("syntax keyword %s used before its definition",
						*h.name))
				}
				return invokeMacro(f.mac, z, ce, top)
			}
		} else if t, ok := globalMacros[h.name]; ok {
			// Free reference to a global macro, including forward references.
			return invokeMacro(t, z, ce, top)
		}
	}
	// ordinary procedure call
	return &Cell{expandExpr(z.Car, ce, top), expandList(z.Cdr, ce, top)}
}

func expandList(q Any, ce *ctFrame, top bool) Any {
	j, ok := q.(*Cell)
	if !ok {
		return expandExpr(q, ce, top)
	}
	if j == Nil {
		return Nil
	}
	return &Cell{expandExpr(j.Car, ce, top), expandList(j.Cdr, ce, top)}
}

func expandIf(z *Cell, ce *ctFrame, top bool) Any {
	args := z.Cdr.(*Cell)
	if args == Nil {
		panic(fmt.Errorf("malformed if"))
	}
	c := expandExpr(args.Car, ce, top)
	rest := args.Cdr.(*Cell)
	if rest == Nil {
		panic(fmt.Errorf("malformed if"))
	}
	th := expandExpr(rest.Car, ce, top)
	r := rest.Cdr.(*Cell)
	if r == Nil {
		return listFrom(ifSym, c, th)
	}
	if r.Cdr != Nil {
		panic(fmt.Errorf("malformed if"))
	}
	return listFrom(ifSym, c, th, expandExpr(r.Car, ce, top))
}

func expandLambda(z *Cell, ce *ctFrame, top bool) Any {
	q := z.Cdr.(*Cell)
	params, ok := q.Car.(*Cell)
	if !ok {
		panic(fmt.Errorf("lambda parameters must be a proper list"))
	}
	body := q.Cdr.(*Cell)
	if body == Nil {
		panic(fmt.Errorf("lambda requires a body"))
	}
	ce1 := ce
	keys := make([]Any, 0, 4)
	for j := params; j != Nil; j = j.Cdr.(*Cell) {
		s, ok := j.Car.(*sid)
		if !ok {
			panic(fmt.Errorf("lambda parameter must be an identifier: %s",
				Stringify(datafy(j.Car), true)))
		}
		g := gensym(s.name)
		keys = append(keys, g)
		ce1 = &ctFrame{name: s.name, tag: s.tag, kind: bindVar, v: g, next: ce1}
	}
	bd, _ := expandSeq(body, ce1, false, true)
	return listFrom(lambdaSym, listFrom(keys...), bd)
}

// expandDefine handles (define var expr); it returns the emitted runtime form
// and the extended compile-time environment.
func expandDefine(z *Cell, ce *ctFrame, top bool) (Any, *ctFrame) {
	q := z.Cdr.(*Cell)
	target := q.Car
	expr := q.Cdr.(*Cell)
	if expr == Nil || expr.Cdr != Nil {
		panic(fmt.Errorf("malformed define"))
	}
	switch s := target.(type) {
	case *sid:
		// Reuse a frame pre-bound by the enclosing body, if any.
		if pre := ce.lookupExact(s); pre != nil && pre.kind == bindVar {
			rhs := expandExpr(expr.Car, ce, top)
			return listFrom(defineSym, pre.v, rhs), ce
		}
		key := s.name
		if !(top && s.tag == nil) {
			key = gensym(s.name)
		}
		rhs := expandExpr(expr.Car, ce, top)
		ce2 := &ctFrame{name: s.name, tag: s.tag, kind: bindVar, v: key, next: ce}
		return listFrom(defineSym, key, rhs), ce2
	case *Symbol: // already resolved through a definition-site tag
		rhs := expandExpr(expr.Car, ce, top)
		return listFrom(defineSym, s, rhs), ce
	default:
		panic(fmt.Errorf("malformed define target"))
	}
}

func expandSetQ(z *Cell, ce *ctFrame, top bool) Any {
	q := z.Cdr.(*Cell)
	target := q.Car
	if q.Cdr.(*Cell) == Nil || q.Cdr.(*Cell).Cdr != Nil {
		panic(fmt.Errorf("malformed set!"))
	}
	val := expandExpr(q.Cdr.(*Cell).Car, ce, top)
	var key *Symbol
	switch s := target.(type) {
	case *sid:
		f := resolveID(s, ce)
		if f == nil {
			key = s.name // free global; set! fails at runtime if unbound, as before
		} else if f.kind == bindVar {
			key = f.v
		} else {
			panic(fmt.Errorf("cannot set! syntax keyword %s", *s.name))
		}
	case *Symbol:
		key = s
	default:
		panic(fmt.Errorf("malformed set! target"))
	}
	return listFrom(setQSym, key, val)
}

func expandDefineSyntax(z *Cell, ce *ctFrame, top bool) *ctFrame {
	q := z.Cdr.(*Cell)
	nm, ok := q.Car.(*sid)
	if !ok {
		panic(fmt.Errorf("define-syntax requires an identifier name"))
	}
	spec := q.Cdr.(*Cell)
	if spec == Nil || spec.Cdr != Nil {
		panic(fmt.Errorf("define-syntax requires one transformer"))
	}
	// Fill a frame pre-bound by the enclosing body, if any; body-level
	// macros are mutually recursive (letrec* style).
	if pre := ce.lookupExact(nm); pre != nil && pre.kind == bindMacro {
		pre.mac = compileTransformer(spec.Car, ce)
		return ce
	}
	// A top-level macro is recursive in its own transformer.
	var self *ctFrame
	ceCompile := ce
	if top && nm.tag == nil {
		self = &ctFrame{name: nm.name, kind: bindMacro, next: ce}
		ceCompile = self
	}
	t := compileTransformer(spec.Car, ceCompile)
	if self != nil {
		self.mac = t
		globalMacros[nm.name] = t
	}
	return &ctFrame{name: nm.name, tag: nm.tag, kind: bindMacro, mac: t, next: ce}
}

func expandLetSyntax(z *Cell, ce *ctFrame, top bool, rec bool) Any {
	q := z.Cdr.(*Cell)
	bindings, ok := q.Car.(*Cell)
	if !ok || bindings == Nil {
		panic(fmt.Errorf("let-syntax requires bindings and a body"))
	}
	body := q.Cdr.(*Cell)
	if body == Nil {
		panic(fmt.Errorf("let-syntax requires a body"))
	}
	type pending struct {
		nm   *sid
		spec Any
		fr   *ctFrame
	}
	var ps []pending
	for j := bindings; j != Nil; j = j.Cdr.(*Cell) {
		b, ok := j.Car.(*Cell)
		if !ok || b == Nil {
			panic(fmt.Errorf("ill-formed local syntax binding"))
		}
		nm, ok := b.Car.(*sid)
		if !ok {
			panic(fmt.Errorf("local syntax binding name must be an identifier"))
		}
		r := b.Cdr.(*Cell)
		if r == Nil || r.Cdr != Nil {
			panic(fmt.Errorf("local syntax binding requires one transformer"))
		}
		ps = append(ps, pending{nm: nm, spec: r.Car})
	}
	// Build the scope chain; the first binding is nearest.
	ce1 := ce
	for i := range ps {
		fr := &ctFrame{name: ps[i].nm.name, tag: ps[i].nm.tag,
			kind: bindMacro, next: ce1}
		ps[i].fr = fr
		ce1 = fr
	}
	for i := range ps {
		compileCE := ce
		if rec {
			compileCE = ce1
		}
		ps[i].fr.mac = compileTransformer(ps[i].spec, compileCE)
	}
	out, _ := expandSeq(body, ce1, top, !top)
	return out
}

// macroDepth guards against non-terminating macro expansion so that such
// errors fail through the normal error channel instead of overflowing the
// Go stack fatally.
var macroDepth int

const macroDepthLimit = 10000

func invokeMacro(t *transformer, z *Cell, ce *ctFrame, top bool) Any {
	macroDepth++
	if macroDepth > macroDepthLimit {
		macroDepth = 0
		panic(fmt.Errorf(
			"macro expansion too deep (possible infinite expansion) at %s",
			Stringify(datafy(z.Car), false)))
	}
	out := t.apply(z, ce)
	res := expandExpr(out, ce, top)
	macroDepth--
	return res
}

//----------------------------------------------------------------------
// Small list builders
//----------------------------------------------------------------------

func listFrom(items ...Any) Any {
	var tail Any = Nil
	for i := len(items) - 1; i >= 0; i-- {
		tail = &Cell{items[i], tail}
	}
	return tail.(*Cell)
}
