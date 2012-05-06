--DEPS: OneDimensionalArrayAggregate PrimitiveArray
#include "axiom.as"

IndexedOneDimensionalArray(S:Type, minIndex:Integer): OneDimensionalArrayAggregate S 
== add {
   Rep ==> PrimitiveArray S;
   import from Rep;
   import from NonNegativeInteger;
   import from Integer;
   
   empty(): % == per new(0);
   elt(x: %, i: Integer): S == rep(x).(i-minIndex);
   new(n: NonNegativeInteger): % == per new(n);
   new(n: NonNegativeInteger, s: S): % == per new(n, s);
   setelt(x: %, i: Integer, s: S): S == setelt(x, i, s);
}
