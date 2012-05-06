--DEPS: LinearAggregate finiteAggregate shallowlyMutable
#include "axiom.as"
#pile
import from Boolean

FiniteLinearAggregate(S:Type): Category == Join(LinearAggregate S,_
     finiteAggregate) 
 with
   merge: ((S,S)->Boolean,%,%) -> %
      ++ merge(p,a,b) returns an aggregate c which merges \axiom{a} and b.
      ++ The result is produced by examining each element x of \axiom{a} and y
      ++ of b successively. If \axiom{p(x,y)} is true, then x is inserted into
      ++ the result; otherwise y is inserted. If x is chosen, the next element
      ++ of \axiom{a} is examined, and so on. When all the elements of one
      ++ aggregate are examined, the remaining elements of the other
      ++ are appended.
      ++ For example, \axiom{merge(<,[1,3],[2,7,5])} returns \axiom{[1,2,3,7,5]}.
   reverse: % -> %
      ++ reverse(a) returns a copy of \axiom{a} with elements in reverse order.
   sort: ((S,S)->Boolean,%) -> %
      ++ sort(p,a) returns a copy of \axiom{a} sorted using total ordering predicate p.
   sorted?: ((S,S)->Boolean,%) -> Boolean
      ++ sorted?(p,a) tests if \axiom{a} is sorted according to predicate p.
   position: (S->Boolean, %) -> Integer
      ++ position(p,a) returns the index i of the first x in \axiom{a} such that
      ++ \axiom{p(x)} is true, and \axiom{minIndex(a) - 1} if there is no such x.
   new: NonNegativeInteger -> %
      ++ creates a new aggregate with the specified number of values, all undefined.
   if S has SetCategory then
      position: (S, %)  -> Integer
        ++ position(x,a) returns the index i of the first occurrence of x in a,
        ++ and \axiom{minIndex(a) - 1} if there is no such x.
      position: (S,%,Integer) -> Integer
        ++ position(x,a,n) returns the index i of the first occurrence of x in
        ++ \axiom{a} where \axiom{i >= n}, and \axiom{minIndex(a) - 1} if no such x is found.
   if S has OrderedSet then
      OrderedSet
      merge: (%,%) -> %
        ++ merge(u,v) merges u and v in ascending order.
        ++ Note: \axiom{merge(u,v) = merge(<=,u,v)}.
      sort: % -> %
        ++ sort(u) returns an u with elements in ascending order.
        ++ Note: \axiom{sort(u) = sort(<=,u)}.
      sorted?: % -> Boolean
        ++ sorted?(u) tests if the elements of u are in ascending order.
   if % has shallowlyMutable then
      copyInto!: (%,%,Integer) -> %
        ++ copyInto!(u,v,i) returns aggregate u containing a copy of
        ++ v inserted at element i.
      reverse!: % -> %
        ++ reverse!(u) returns u with its elements in reverse order.
      sort!: ((S,S)->Boolean,%) -> %
        ++ sort!(p,u) returns u with its elements ordered by p.
      if S has OrderedSet then 
        sort!: % -> %
          ++ sort!(u) returns u with its elements in ascending order.
   default
    if S has SetCategory then
      default l: %
      default f: (S, S) -> Boolean

      new(n: NonNegativeInteger): % == never

      position(s:S, t:%): Integer == position(s, t, minIndex t)

    if S has OrderedSet then
--    sorted?(l): Boolean   == sorted?(_<$S, l)
      sorted?(l): Boolean   == sorted?((x: S, y: S): Boolean +-> x < y or x = y, l)
      merge(x: %, y: %): % == merge(_<$S, x, y)
      sort l: %      == sort(_<$S, l)

    if % has shallowlyMutable then
      reverse(x: %): %  == reverse! copy x
      sort(f, l): % == sort!(f, copy l)

      if S has OrderedSet then
        sort!(l): % == sort!(_<$S, l)

