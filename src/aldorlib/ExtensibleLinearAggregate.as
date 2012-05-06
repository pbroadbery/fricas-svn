--DEPS: LinearAggregate shallowlyMutable OrderedSet
#include "axiom.as"

#pile
import from Boolean

ExtensibleLinearAggregate(S:Type):Category == Join(LinearAggregate S,_
     shallowlyMutable) with
 concat!: (%,S) -> %
     ++ concat!(u,x) destructively adds element x to the end of u.
 concat!: (%,%) -> %
     ++ concat!(u,v) destructively appends v to the end of u.
     ++ v is unchanged
 delete!: (%,Integer) -> %
     ++ delete!(u,i) destructively deletes the \axiom{i}th element of u.
 delete!: (%,UniversalSegment(Integer)) -> %
     ++ delete!(u,i..j) destructively deletes elements u.i through u.j.
 remove!: (S->Boolean,%) -> %
     ++ remove!(p,u) destructively removes all elements x of
     ++ u such that \axiom{p(x)} is true.
 insert!: (S,%,Integer) -> %
     ++ insert!(x,u,i) destructively inserts x into u at position i.
 insert!: (%,%,Integer) -> %
     ++ insert!(v,u,i) destructively inserts aggregate v into u at position i.
 merge!: ((S,S)->Boolean,%,%) -> %
     ++ merge!(p,u,v) destructively merges u and v using predicate p.
 select!: (S->Boolean,%) -> %
     ++ select!(p,u) destructively changes u by keeping only values x such that
     ++ \axiom{p(x)}.
 if S has SetCategory then
     remove!: (S,%) -> %
       ++ remove!(x,u) destructively removes all values x from u.
     removeDuplicates!: % -> %
       ++ removeDuplicates!(u) destructively removes duplicates from u.
 if S has OrderedSet then 
     merge!: (%,%) -> %
       ++ merge!(u,v) destructively merges u and v in ascending order.
 default
   import from NonNegativeInteger
   import from Integer
   delete(x:%, i:Integer): %          == delete!(copy x, i)
   delete(x:%, i:UniversalSegment(Integer)): %        == delete!(copy x, i)
   remove(f:S -> Boolean, x:%): %   == remove!(f, copy x)
   insert(s:S, x:%, i:Integer): %   == insert!(s, copy x, i)
   insert(w:%, x:%, i:Integer): %   == insert!(copy w, copy x, i)
   _select(f: S -> Boolean, x: %): %            == select!(f, copy x)
   concat(x:%, y:%): %        == concat!(copy x, y)
   concat(x:%, y:S): %        == concat!(copy x, new(1, y))
   concat!(x:%, y:S): %      == concat!(x, new(1, y))
   if S has SetCategory then
     remove(s:S, x:%): %       == remove!(s, copy x)
     remove!(s : S, x : %): %  == remove!((y: S): Boolean +-> y = s, x)
     removeDuplicates(x:%): %  == removeDuplicates!(copy x)

   if S has OrderedSet then
     merge!(x: %, y: %): % == merge!(_<$S, x, y)

