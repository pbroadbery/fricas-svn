#include "axiom.as"

import from Boolean;

ListAggregate(S:Type): Category == Join(StreamAggregate S,
   FiniteLinearAggregate S, ExtensibleLinearAggregate S) with
      list: S -> %
        ++ list(x) returns the list of one element x.
 add
   cycleMax ==> 1000

   mergeSort: ((S, S) -> Boolean, %, Integer) -> %

   sort!(f, l)       == mergeSort(f, l, #l)
   list x                  == concat(x, empty())
   reduce(f, x)            ==
     empty? x => error "reducing over an empty list needs the 3 argument form"
     reduce(f, rest x, first x)
   merge(f, p, q)          == merge!(f, copy p, copy q)

   select!(f, x) ==
     while not empty? x and not f first x repeat x := rest x
     empty? x => x
     y := x
     z := rest y
     while not empty? z repeat
       if f first z then (y := z; z := rest z)
                    else (z := rest z; setrest!(y, z))
     x

   merge!(f, p, q) ==
     empty? p => q
     empty? q => p
     eq?(p, q) => error "cannot merge a list into itself"
     if f(first p, first q)
       then (r := t := p; p := rest p)
       else (r := t := q; q := rest q)
     while not empty? p and not empty? q repeat
       if f(first p, first q)
         then (setrest!(t, p); t := p; p := rest p)
         else (setrest!(t, q); t := q; q := rest q)
     setrest!(t, if empty? p then q else p)
     r

   insert!(s:S, x:%, i:Integer) ==
     i < (m := minIndex x) => error "index out of range"
     i = m => concat(s, x)
     y := rest(x, (i - 1 - m)::NonNegativeInteger)
     z := rest y
     setrest!(y, concat(s, z))
     x

   insert!(w:%, x:%, i:Integer) ==
     i < (m := minIndex x) => error "index out of range"
     i = m => concat!(w, x)
     y := rest(x, (i - 1 - m)::NonNegativeInteger)
     z := rest y
     setrest!(y, w)
     concat!(y, z)
     x

   remove!(f:S -> Boolean, x:%) ==
     while not empty? x and f first x repeat x := rest x
     empty? x => x
     p := x
     q := rest x
     while not empty? q repeat
       if f first q then q := setrest!(p, rest q)
                    else (p := q; q := rest q)
     x

   delete!(x:%, i:Integer) ==
     i < (m := minIndex x) => error "index out of range"
     i = m => rest x
     y := rest(x, (i - 1 - m)::NonNegativeInteger)
     setrest!(y, rest(y, 2))
     x

   delete!(x:%, i:UniversalSegment(Integer)) ==
     (l := lo i) < (m := minIndex x) => error "index out of range"
     h := if hasHi i then hi i else maxIndex x
     h < l => x
     l = m => rest(x, (h + 1 - m)::NonNegativeInteger)
     t := rest(x, (l - 1 - m)::NonNegativeInteger)
     setrest!(t, rest(t, (h - l + 2)::NonNegativeInteger))
     x

   find(f, x) ==
     while not empty? x and not f first x repeat x := rest x
     empty? x => "failed"
     first x

   position(f:S -> Boolean, x:%) ==
     for k in minIndex(x).. while not empty? x and not f first x repeat
       x := rest x
     empty? x => minIndex(x) - 1
     k

   mergeSort(f, p, n) ==
     if n = 2 and f(first rest p, first p) then p := reverse! p
     n < 3 => p
     l := (n quo 2)::NonNegativeInteger
     q := split!(p, l)
     p := mergeSort(f, p, l)
     q := mergeSort(f, q, n - l)
     merge!(f, p, q)

   sorted?(f, l) ==
     empty? l => true
     p := rest l
     while not empty? p repeat
       not f(first l, first p) => return false
       p := rest(l := p)
     true

   reduce(f, x, i) ==
     r := i
     while not empty? x repeat (r := f(r, first x); x := rest x)
     r

   if S has SetCategory then
      reduce(f, x, i,a) ==
        r := i
        while not empty? x and r ~= a repeat
          r := f(r, first x)
          x := rest x
        r

   new(n, s) ==
     l := empty()
     for k in 1..n repeat l := concat(s, l)
     l

   map(f, x, y) ==
     z := empty()
     while not empty? x and not empty? y repeat
       z := concat(f(first x, first y), z)
       x := rest x
       y := rest y
     reverse! z

-- map(f, x, y, d) ==
--   z := empty()
--   while not empty? x and not empty? y repeat
--     z := concat(f(first x, first y), z)
--     x := rest x
--     y := rest y
--   z := reverseInPlace z
--   if not empty? x then
--      z := concat!(z, map(f(#1, d), x))
--   if not empty? y then
--      z := concat!(z, map(f(d, #1), y))
--   z

   reverse! x ==
     empty? x => x
     empty?(y := rest x) => x
     setrest!(x, empty())
     while not empty? y repeat
       z := rest y
       setrest!(y, x)
       x := y
       y := z
     x

   copy x ==
     y := empty()
     for k in 0.. while not empty? x repeat
       k = cycleMax and cyclic? x => error "cyclic list"
       y := concat(first x, y)
       x := rest x
     reverse! y

   copyInto!(y, x, s) ==
     s < (m := minIndex y) => error "index out of range"
     z := rest(y, (s - m)::NonNegativeInteger)
     while not empty? z and not empty? x repeat
       setfirst!(z, first x)
       x := rest x
       z := rest z
     y

   if S has SetCategory then
     position(w, x, s) ==
       s < (m := minIndex x) => error "index out of range"
       x := rest(x, (s - m)::NonNegativeInteger)
       for k in s.. while not empty? x and w ~= first x repeat
         x := rest x
       empty? x => minIndex x - 1
       k

     removeDuplicates! l ==
       p := l
       while not empty? p repeat
         p := setrest!(p, remove!((x : S) : Boolean +-> x = first p, rest p))
       l

   if S has OrderedSet then
     x < y ==
        while not empty? x and not empty? y repeat
          first x ~= first y => return(first x < first y)
          x := rest x
          y := rest y
        empty? x => not empty? y
        false
