#include "axiom.as"

import from Boolean;

HomogeneousAggregate(S:Type): Category == Aggregate with {
   if S has CoercibleTo(OutputForm) then CoercibleTo(OutputForm);
   if S has SetCategory then SetCategory;
   if S has SetCategory then
      if S has Evalable S then Evalable S;
   map     : (S->S,%) -> %;
     ++ map(f,u) returns a copy of u with each element x replaced by f(x).
     ++ For collections, \axiom{map(f,u) = [f(x) for x in u]}.
   if % has shallowlyMutable then {
     map!: (S->S,%) -> %;
        ++ map!(f,u) destructively replaces each element x of u by \axiom{f(x)}.
   }
   if % has finiteAggregate then {
      any?: (S->Boolean,%) -> Boolean;
        ++ any?(p,u) tests if \axiom{p(x)} is true for any element x of u.
        ++ Note: for collections,
        ++ \axiom{any?(p,u) = reduce(or,map(f,u),false,true)}.
        ++ However, \axiom{any?(p,u)} returns as soon as it finds an element
        ++ for which \axiom{p} gives true.
      every?: (S->Boolean,%) -> Boolean;
        ++ every?(f,u) tests if p(x) is true for all elements x of u.
        ++ Note: for collections,
        ++ \axiom{every?(p,u) = reduce(and,map(f,u),true,false)}.
        ++ However, \axiom{every?(p,u)} returns as soon as it finds an element
        ++ for which \axiom{p} gives false.
      count: (S->Boolean,%) -> NonNegativeInteger;
        ++ count(p,u) returns the number of elements x in u
        ++ such that \axiom{p(x)} is true. For collections,
        ++ \axiom{count(p,u) = reduce(+,[1 for x in u | p(x)],0)}.
      parts: % -> List S;
        ++ parts(u) returns a list of the consecutive elements of u.
        ++ For collections, \axiom{parts([x,y,...,z]) = (x,y,...,z)}.
      members: % -> List S;
        ++ members(u) returns a list of the consecutive elements of u.
        ++ For collections, \axiom{parts([x,y,...,z]) = (x,y,...,z)}.
      if S has SetCategory then {
        count: (S,%) -> NonNegativeInteger;
          ++ count(x,u) returns the number of occurrences of x in u.
          ++ For collections, \axiom{count(x,u) = reduce(+,[x=y for y in u],0)}.
        member?: (S,%) -> Boolean;
          ++ member?(x,u) tests if x is a member of u.
          ++ For collections,
          ++ \axiom{member?(x,u) = reduce(or,[x=y for y in u],false)}.
          ++ However, \axiom{member?(x,u)} returns as soon as it finds a
          ++ member.
     }
    }
  default {
   default f: S -> Boolean;
   default e: S;
   default c, c1, c2: %;
   import from S;
   if S has Evalable S then
     eval(u : %, l : List Equation S) : % == map((x: S): S +-> eval(x, l), u);
   if % has finiteAggregate then {
     import from List S;
     #c: NonNegativeInteger  == # parts c;
     any?(f, c): Boolean == {
       for x in parts c | f x repeat return true;
       false}
     every?(f, c): Boolean == {
       for x in parts c | not f x repeat return false;
       true}
     count(f:S -> Boolean, c:%): NonNegativeInteger == {
             import from Fold(NonNegativeInteger, 0);
	     import from List NonNegativeInteger;
	     import from NonNegativeInteger;
	     _+/[1 for x in parts c | f x];
     }
     members(c): List S == parts c;
     if S has SetCategory then {
       count(s : S, c: %): NonNegativeInteger == count((y:S): Boolean +-> s = y, c);
       member?(e, c): Boolean == any?((x: S): Boolean +-> e = x, c);
       c1 = c2: Boolean == {
          not size?(c1, #c2) => false;
          for a in parts c1 for b in parts c2 | a ~= b repeat return false;
          true}
       coerce(x:%):OutputForm == {
	 import from List OutputForm;
         bracket commaSeparate([a::OutputForm for a in parts x]$List(OutputForm));
       }
}}}}