--DEPS: FiniteSetAggregate FlexibleArray InputForm
#include "axiom.as"

#pile
import from System
import from String

Set(S:SetCategory): FiniteSetAggregate S == add
   Rep == FlexibleArray(S)
   import from UniversalSegment Integer
   import from NonNegativeInteger
   import from Integer
   import from Rep
   default s, t: %
   default l: List S
   default x: S

   local apply(s: %, i: Integer): S == rep(s).i

   # s: NonNegativeInteger       == #rep(s)
   brace(): %   == empty()
   set(): %     == empty()
   empty(): %   == per(empty()$Rep)
   copy s: %    == per(copy(rep s)$Rep)
   parts s: List S == parts(rep s)$Rep
   inspect s: S == (empty? s => error "Empty set"; s(maxIndex rep s))

   extract! s: S ==
     x := inspect(s)
     delete!(rep s, maxIndex rep s)
     x

   -- Following NOT IN algebra/
   index(p: PositiveInteger): % == never

   find(f: S -> Boolean, s): Partial S == find(f, rep s)$Rep

   map(f: S -> S, s): % == map!(f,copy s)

   reduce(f: (S, S) -> S, s): S == reduce(f, rep s)$Rep

   reduce(f: (S, S) -> S, s, x: S): S == reduce(f, rep s, x)$Rep

   reduce(f: (S, S) -> S, s, x: S, y: S): S == reduce(f, rep s, x, y)$Rep

   if S has ConvertibleTo InputForm then
     convert(a:%): InputForm ==
        import from List InputForm
        import from Symbol
        convert([convert(#"set")@InputForm,
                          convert(parts a)@InputForm])$InputForm

   if S has OrderedSet then
     s = t: Boolean == rep(s) = rep(t)
     max s: S == inspect s
     min s: S == (empty? s => error "Empty set"; s(minIndex rep s))

     map!(f: S-> S,s): % ==
        map!(f,rep s)$Rep
        sort!(rep s)$Rep
        per removeRepeats! rep s

     construct l: % ==
       zero?(n := #l) => empty()
       a: Rep := new(n, first l)
       for i in minIndex(a).. for x in l repeat a.i := x
       per removeRepeats! sort! a

     insert!(x, s): % ==
       n := inc maxIndex rep s
       k := minIndex rep s
       while k < n and x > s.k repeat k := inc k
       k < n and s.k = x => s
       per insert!(x, rep s, k)

     member?(x, s): Boolean == -- binary search
       empty? s => false
       tt: Integer := maxIndex rep s
       b := minIndex rep s
       while b < tt repeat
         m := (b+tt) quo 2
         if x > s.m then b := m+1 else tt := m
       x = s.tt

     remove!(x:S, s:%): % ==
       n := inc maxIndex rep s
       k := minIndex rep s
       while k < n and x > s.k repeat k := inc k
       k < n and x = s.k => per delete!(rep s, k)
       s

     -- the set operations are implemented as variations of merging
     intersect(s, t): % ==
       m: Integer := maxIndex rep s
       n: Integer := maxIndex rep t
       i: Integer := minIndex rep s
       j: Integer := minIndex rep t
       r: % := empty()
       while i <= m and j <= n repeat
         s.i = t.j => (concat!(rep r, s.i); i := i+1; j := j+1)
         if s.i < t.j then i := i+1 else j := j+1
       r

     difference(s:%, t:%): % ==
       m: Integer := maxIndex rep s
       n: Integer := maxIndex rep t
       i: Integer := minIndex rep s
       j: Integer := minIndex rep t
       r: % := empty()
       while i <= m and j <= n repeat
         s.i = t.j => (i := i+1; j := j+1)
         s.i < t.j => (concat!(rep r, s.i); i := i+1)
         j := j+1
       while i <= m repeat (concat!(rep r, s.i); i := i+1)
       r

     symmetricDifference(s, t): % ==
       m := maxIndex rep s
       n := maxIndex rep t
       i := minIndex rep s
       j := minIndex rep t
       r: % := empty()
       while i <= m and j <= n repeat
         s.i < t.j => (concat!(rep r, s.i); i := i+1)
         s.i > t.j => (concat!(rep r, t.j); j := j+1)
         i := i+1; j := j+1
       while i <= m repeat (concat!(rep r, s.i); i := i+1)
       while j <= n repeat (concat!(rep r, t.j); j := j+1)
       r

     subset?(s, t): Boolean ==
       m := maxIndex rep s
       n := maxIndex rep t
       m > n => false
       i := minIndex rep s
       j := minIndex rep t
       while i <= m and j <= n repeat
         s.i = t.j => (i := i+1; j := j+1)
         s.i > t.j => j := j+1
         return false
       i > m

     union(s:%, t:%): % ==
       m := maxIndex rep s
       n := maxIndex rep t
       i := minIndex rep s
       j := minIndex rep t
       r: % := empty()
       while i <= m and j <= n repeat
         s.i = t.j => (concat!(rep r, s.i); i := i+1; j := j+1)
         s.i < t.j => (concat!(rep r, s.i); i := i+1)
         (concat!(rep r, t.j); j := j+1)
       while i <= m repeat (concat!(rep r, s.i); i := i+1)
       while j <= n repeat (concat!(rep r, t.j); j := j+1)
       r

    else
      insert!(x, s): % ==
        for k in minIndex rep s .. maxIndex rep s repeat
          s.k = x => return s
        per insert!(x, rep s, inc maxIndex rep s)

      remove!(x:S, s:%): % ==
        n := inc maxIndex rep s
        k := minIndex rep s
        while k < n repeat
          x = s.k => return per delete!(rep s, k)
          k := inc k
        s

      map!(f: S -> S, s): % ==
        map!(f, rep s)$Rep
        per removeDuplicates! rep s
