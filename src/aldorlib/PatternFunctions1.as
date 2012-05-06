--DEPS: init_Pattern SetCategory List Symbol Any AnyFunctions1 init_Pattern
#include "axiom.as"
#pile

PatternFunctions1(R:SetCategory, D:Type): with
    suchThat   : (Pattern R, D -> Boolean)       -> Pattern R
      ++ suchThat(p, f) makes a copy of p and adds the predicate
      ++ f to the copy, which is returned.
    suchThat   : (Pattern R, List(D -> Boolean)) -> Pattern R
      ++ \spad{suchThat(p, [f1,...,fn])} makes a copy of p and adds the
      ++ predicate f1 and ... and fn to the copy, which is returned.
    suchThat : (Pattern R, List Symbol, List D -> Boolean)  -> Pattern R
      ++ \spad{suchThat(p, [a1,...,an], f)} returns a copy of p with
      ++ the top-level predicate set to \spad{f(a1,...,an)}.
    predicate  : Pattern R -> (D -> Boolean)
      ++ predicate(p) returns the predicate attached to p, the
      ++ constant function true if p has no predicates attached to it.
    satisfy?   : (D, Pattern R) -> Boolean
      ++ satisfy?(v, p) returns f(v) where f is the predicate
      ++ attached to p.
    satisfy?   : (List D, Pattern R) -> Boolean
      ++ \spad{satisfy?([v1,...,vn], p)} returns \spad{f(v1,...,vn)}
      ++ where f is the
      ++ top-level predicate attached to p.
    addBadValue: (Pattern R, D) -> Pattern R
      ++ addBadValue(p, v) adds v to the list of "bad values" for p;
      ++ p is not allowed to match any of its "bad values".
    badValues  : Pattern R -> List D
      ++ badValues(p) returns the list of "bad values" for p;
      ++ p is not allowed to match any of its "bad values".
  == add
    A1D ==> AnyFunctions1(D)
    A1  ==> AnyFunctions1(D -> Boolean)
    A1L ==> AnyFunctions1(List D -> Boolean)
    
    default p: Pattern R
    default l: List Any
    default d, v: D

    local st(p, l): Pattern R          == withPredicates(p, concat(predicates p, l))
    predicate p: (D -> Boolean)       == (d1: D): Boolean +-> applyAll(predicates p, d1)
    addBadValue(p, v): Pattern R == addBadValue(p, coerce(v)$A1D)
    badValues p: List D       == [retract(v)$A1D for v in getBadValues p]
    suchThat(p, l, f: D -> Boolean): Pattern R == setTopPredicate(copy p, l, coerce(f)$A1L)
    suchThat(p:Pattern R, f:D -> Boolean): Pattern R == st(p, [coerce(f)$A1])
    satisfy?(d:D, p:Pattern R): Boolean == applyAll(predicates p, d)

    satisfy?(l:List D, p:Pattern R): Boolean ==
      empty?((rec := topPredicate p).var) => true
      retract(rec.pred) l

    local applyAll(l, d): Boolean ==
      for f in l repeat
        not(retract(f) d) => return false
      true

    suchThat(p:Pattern R, l:List(D -> Boolean)): Pattern R ==
      st(p, [coerce(f) for f in l])

