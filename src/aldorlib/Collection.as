--DEPS:  HomogeneousAggregate Partial init_InputForm ConvertibleTo
#include "axiom.as"

import from Boolean;

Collection(S:Type): Category == HomogeneousAggregate(S) with {
   construct: List S -> %;
     ++ \axiom{construct(x,y,...,z)} returns the collection of elements \axiom{x,y,...,z}
     ++ ordered as given. Equivalently written as \axiom{[x,y,...,z]$D}, where
     ++ D is the domain. D may be omitted for those of type List.
   find: (S->Boolean, %) -> Partial S;
     ++ find(p,u) returns the first x in u such that \axiom{p(x)} is true, and
     ++ "failed" otherwise.
   if % has finiteAggregate then {
      reduce: ((S,S)->S,%) -> S;
        ++ reduce(f,u) reduces the binary operation f across u. For example,
        ++ if u is \axiom{[x,y,...,z]} then \axiom{reduce(f,u)} returns \axiom{f(..f(f(x,y),...),z)}.
        ++ Note: if u has one element x, \axiom{reduce(f,u)} returns x.
        ++ Error: if u is empty.
      reduce: ((S,S)->S,%,S) -> S;
        ++ reduce(f,u,x) reduces the binary operation f across u, where x is
        ++ the identity operation of f.
        ++ Same as \axiom{reduce(f,u)} if u has 2 or more elements.
        ++ Returns \axiom{f(x,y)} if u has one element y,
        ++ x if u is empty.
        ++ For example, \axiom{reduce(+,u,0)} returns the
        ++ sum of the elements of u.
      remove: (S->Boolean,%) -> %;
        ++ remove(p,u) returns a copy of u removing all elements x such that
        ++ \axiom{p(x)} is true.
        ++ Note: \axiom{remove(p,u) == [x for x in u | not p(x)]}.
      _select: (S->Boolean,%) -> %;
        ++ select(p,u) returns a copy of u containing only those elements such
        ++ \axiom{p(x)} is true.
        ++ Note: \axiom{select(p,u) == [x for x in u | p(x)]}.
      if S has SetCategory then {
        reduce: ((S,S)->S,%,S,S) -> S;
          ++ reduce(f,u,x,z) reduces the binary operation f across u, stopping
          ++ when an "absorbing element" z is encountered.
          ++ As for \axiom{reduce(f,u,x)}, x is the identity operation of f.
          ++ Same as \axiom{reduce(f,u,x)} when u contains no element z.
          ++ Thus the third argument x is returned when u is empty.
        remove: (S,%) -> %;
          ++ remove(x,u) returns a copy of u with all
          ++ elements \axiom{y = x} removed.
          ++ Note: \axiom{remove(y,c) == [x for x in c | x ~= y]}.
        removeDuplicates: % -> %;
          ++ removeDuplicates(u) returns a copy of u with all duplicates removed.
   }
   }
   if S has ConvertibleTo InputForm then ConvertibleTo InputForm;
 default {
   import from List S;
   if % has finiteAggregate then {
     find(f:S -> Boolean, c:%): Partial S == find(f, parts c);
     reduce(f:(S,S)->S, x:%): S == reduce(f, parts x);
     reduce(f:(S,S)->S, x:%, s:S): S == reduce(f, parts x, s);
     remove(f:S->Boolean, x:%): % == construct remove(f, parts x);
     _select(f:S->Boolean, x:%): % == construct _select(f, parts x);

     if S has SetCategory then {
       remove(s : S, x : %): % == remove((y: S):Boolean +-> y = s, x);
       reduce(f:(S,S)->S, x:%, s1:S, s2:S): S == reduce(f, parts x, s1, s2);
       removeDuplicates(x: %): % == construct removeDuplicates parts x;
     }
     if S has ConvertibleTo InputForm then {
 
         convert(x : %) : InputForm == {
	       never;
--             p_form : List(InputForm) :=
--                 [convert(el)@InputForm for el in parts(x)];
--             l_form := cons(convert('construct)@InputForm, p_form);
--             a_form := convert(l_form)@InputForm;
--             packageCall('construct, [a_form])$InputFormFunctions1(%);
}
}
}
}
}