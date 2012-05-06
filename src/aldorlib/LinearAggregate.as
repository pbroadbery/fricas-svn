--DEPS: Collection IndexedAggregate init_NonNegativeInteger 
--DEPS: Integer_OrderedRing init_UniversalSegment Segment_SegmentCategory
#include "axiom.as"

import from Boolean;

LinearAggregate(S:Type): Category ==
  Join(IndexedAggregate(Integer, S), Collection(S)) with {
   generator: % -> Generator S;
   new   : (NonNegativeInteger,S) -> %;
     ++ new(n,x) returns \axiom{fill!(new n,x)}.
   concat: (%,S) -> %;
     ++ concat(u,x) returns aggregate u with additional element x at the end.
     ++ Note: for lists, \axiom{concat(u,x) == concat(u,[x])}
   concat: (S,%) -> %;
     ++ concat(x,u) returns aggregate u with additional element at the front.
     ++ Note: for lists: \axiom{concat(x,u) == concat([x],u)}.
   concat: (%,%) -> %;
      ++ concat(u,v) returns an aggregate consisting of the elements of u
      ++ followed by the elements of v.
      ++ Note: if \axiom{w = concat(u,v)} then \axiom{w.i = u.i for i in indices u}
      ++ and \axiom{w.(j + maxIndex u) = v.j for j in indices v}.
   concat: List % -> %;
      ++ concat(u), where u is a lists of aggregates \axiom{[a,b,...,c]}, returns
      ++ a single aggregate consisting of the elements of \axiom{a}
      ++ followed by those
      ++ of b followed ... by the elements of c.
      ++ Note: \axiom{concat(a,b,...,c) = concat(a,concat(b,...,c))}.
   map: ((S,S)->S,%,%) -> %;
     ++ map(f,u,v) returns a new collection w with elements \axiom{z = f(x,y)}
     ++ for corresponding elements x and y from u and v.
     ++ Note: for linear aggregates, \axiom{w.i = f(u.i,v.i)}.
   elt: (%,UniversalSegment(Integer)) -> %;
      ++ elt(u,i..j) (also written: \axiom{a(i..j)}) returns the aggregate of
      ++ elements \axiom{u} for k from i to j in that order.
      ++ Note: in general, \axiom{a.s = [a.k for i in s]}.
   apply: (%,UniversalSegment(Integer)) -> %;
      ++ apply(u,i..j) (also written: \axiom{a(i..j)}) returns the aggregate of
      ++ elements \axiom{u} for k from i to j in that order.
      ++ Note: in general, \axiom{a.s = [a.k for i in s]}.
   delete: (%,Integer) -> %;
      ++ delete(u,i) returns a copy of u with the \axiom{i}th element deleted.
      ++ Note: for lists, \axiom{delete(a,i) == concat(a(0..i - 1),a(i + 1,..))}.
   delete: (%,UniversalSegment(Integer)) -> %;
      ++ delete(u,i..j) returns a copy of u with the \axiom{i}th through
      ++ \axiom{j}th element deleted.
      ++ Note: \axiom{delete(a,i..j) = concat(a(0..i-1),a(j+1..))}.
   insert: (S,%,Integer) -> %;
      ++ insert(x,u,i) returns a copy of u having x as its \axiom{i}th element.
      ++ Note: \axiom{insert(x,a,k) = concat(concat(a(0..k-1),x),a(k..))}.
   insert: (%,%,Integer) -> %;
      ++ insert(v,u,k) returns a copy of u having v inserted beginning at the
      ++ \axiom{i}th element.
      ++ Note: \axiom{insert(v,u,k) = concat( u(0..k-1), v, u(k..) )}.
   if % has shallowlyMutable then {setelt: (%,UniversalSegment(Integer),S) -> S;
      ++ setelt(u,i..j,x) (also written: \axiom{u(i..j) := x}) destructively
      ++ replaces each element in the segment \axiom{u(i..j)} by x.
      ++ The value x is returned.
      ++ Note: u is destructively change so
      ++ that \axiom{u.k := x for k in i..j};
      ++ its length remains unchanged.
    }
 default {
  import from Segment Integer;
  import from NonNegativeInteger;

  indices(a: %): List Integer == [i for i in minIndex a .. maxIndex a];
  index?(i: Integer, a: %): Boolean   == i >= minIndex a and i <= maxIndex a;
  concat(a:%, x:S): %      == concat(a, new(1, x));
  concat(x:S, y:%): %      == concat(new(1, x), y);
  insert(x:S, a:%, i:Integer): % == insert(new(1, x), a, i);
  
  -- default implementation is very bad for linked lists.. remember to
  -- override in recursive aggregate!
  generator(a: %): Generator S == a.i for i in minIndex a .. maxIndex a;

  if % has finiteAggregate then
    maxIndex(l: %): Integer == #l - 1 + minIndex l;
  }

  default apply(a: %, u: UniversalSegment(Integer)): % == never;
}