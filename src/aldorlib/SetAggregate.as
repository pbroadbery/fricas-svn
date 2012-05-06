--DEPS: Collection PartialOrder
#include "axiom.as"
#pile

SetAggregate(S:SetCategory):
  Category == Join(SetCategory, Collection(S), PartialOrder) with
   brace       : () -> %
     ++ brace()$D (otherwise written {}$D)
     ++ creates an empty set aggregate of type D.
     ++ This form is considered obsolete. Use \axiomFun{set} instead.
   brace       : List S -> %
     ++ brace([x,y,...,z])
     ++ creates a set aggregate containing items x,y,...,z.
     ++ This form is considered obsolete. Use \axiomFun{set} instead.
   set         : () -> %
     ++ set()$D creates an empty set aggregate of type D.
   set         : List S -> %
     ++ set([x,y,...,z]) creates a set aggregate containing items x,y,...,z.
   intersect: (%, %) -> %
     ++ intersect(u,v) returns the set aggregate w consisting of
     ++ elements common to both set aggregates u and v.
     ++ Note: equivalent to the notation (not currently supported)
     ++ {x for x in u | member?(x,v)}.
   difference  : (%, %) -> %
     ++ difference(u,v) returns the set aggregate w consisting of
     ++ elements in set aggregate u but not in set aggregate v.
     ++ If u and v have no elements in common, \axiom{difference(u,v)}
     ++ returns a copy of u.
     ++ Note: equivalent to the notation (not currently supported)
     ++ \axiom{{x for x in u | not member?(x,v)}}.
   difference  : (%, S) -> %
     ++ difference(u,x) returns the set aggregate u with element x removed.
     ++ If u does not contain x, a copy of u is returned.
     ++ Note: \axiom{difference(s, x) = difference(s, {x})}.
   symmetricDifference : (%, %) -> %
     ++ symmetricDifference(u,v) returns the set aggregate of elements x which
     ++ are members of set aggregate u or set aggregate v but not both.
     ++ If u and v have no elements in common, \axiom{symmetricDifference(u,v)}
     ++ returns a copy of u.
     ++ Note: \axiom{symmetricDifference(u,v) = union(difference(u,v),difference(v,u))}
   subset?     : (%, %) -> Boolean
     ++ subset?(u,v) tests if u is a subset of v.
     ++ Note: equivalent to
     ++ \axiom{reduce(and,{member?(x,v) for x in u},true,false)}.
   union       : (%, %) -> %
     ++ union(u,v) returns the set aggregate of elements which are members
     ++ of either set aggregate u or v.
   union       : (%, S) -> %
     ++ union(u,x) returns the set aggregate u with the element x added.
     ++ If u already contains x, \axiom{union(u,x)} returns a copy of u.
   union       : (S, %) -> %
     ++ union(x,u) returns the set aggregate u with the element x added.
     ++ If u already contains x, \axiom{union(x,u)} returns a copy of u.
   default
    default x, y: %
    import from List S
    symmetricDifference(x, y): %    == union(difference(x, y), difference(y, x))
    union(s:%, e:S): % == union(s, set([e]))
    union(e:S, s:%): % == union(s, set([e]))
    difference(s:%, e:S): % == difference(s, set([e]))
