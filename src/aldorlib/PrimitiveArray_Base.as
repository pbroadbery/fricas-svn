--DEPS: init_PrimitiveArray NonNegativeInteger Integer init_List runtime/ARCH/Local
#include "axiom.as"

#pile

extend PrimitiveArray(S:Type): TheArray with
   #: % -> NonNegativeInteger
   minIndex: % -> Integer
   empty: () -> %
   new: NonNegativeInteger -> %
   new: (NonNegativeInteger, S) -> %
   qelt: (%, Integer) -> S
   elt: (%, Integer) -> S
   apply: (%, Integer) -> S
   qsetelt!: (%, Integer, S) -> S
   setelt: (%, Integer, S) -> S
   set!: (%, Integer, S) -> S
   construct: List S -> %;
 == add

   Qmax ==> QVMAXINDEX$ArrayLisp(S)
   Qsize ==> QVSIZE$ArrayLisp(S)
   Qelt ==> QAREF1$ArrayLisp(S)
   Qsetelt ==> QSETAREF1$ArrayLisp(S)
   Qnew ==> MAKE_-ARRAY$ArrayLisp(S)
   Qnew1 ==> MAKEARR1$ArrayLisp(S)

   Rep ==> ArrayLisp S
   import from ArrayLisp(S)

   default x: %
   default n: NonNegativeInteger
   default i: Integer
   default s: S

   #x: NonNegativeInteger      == coerce Qsize rep x
   minIndex(x): Integer        == 0
   maxIndex(x): Integer        == #x - 1;
   empty(): %                  == per Qnew(0)
   new(n): %                   == per Qnew(n::Integer)
   new(n, s): %                == per Qnew1(n::Integer, s)

   apply(x, i): S	       == elt(x, i)
   qelt(x, i): S               == elt(x, i)
   elt(x:%, i:Integer): S      == Qelt(rep x, i)

   qsetelt!(x, i, s): S           == setelt(x, i, s)
   set!(x:%, i:Integer, s:S): S == setelt(x, i, s)
   setelt(x:%, i:Integer, s:S): S == { Qsetelt(rep x, i, s); s}

   construct(l: List S): % == never;
