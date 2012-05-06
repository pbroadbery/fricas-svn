--DEPS: XLisp init_PrimitiveArray init_NonNegativeInteger Integer init_List
#include "axiom.as"

#pile

extend PrimitiveArray(S:Type): with
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

   Qmax ==> QVMAXINDEX$XLisp
   Qsize ==> QVSIZE$XLisp
   Qelt ==> QAREF1$XLisp
   Qsetelt ==> QSETAREF1$XLisp
   Qnew ==> MAKE_-ARRAY$XLisp
   Qnew1 ==> MAKEARR1$XLisp

   lrep(x) ==> lisp(%)(x)
   lper(x) ==> unlisp(%)(x)

   irep(x) ==> lisp(Integer)(x)
   iper(x) ==> unlisp(Integer)(x)

   nrep(x) ==> lisp(NonNegativeInteger)(x)
   nper(x) ==> unlisp(NonNegativeInteger)(x)

   srep(x) ==> lisp(S)(x)
   sper(x) ==> unlisp(S)(x);

   import from XLisp

   default x: %
   default n: NonNegativeInteger
   default i: Integer
   default s: S

   #x: NonNegativeInteger      == nper Qsize lrep x
   minIndex(x): Integer        == 0
   maxIndex(x): Integer        == iper(Qmax(lrep x));
   empty(): %                  == lper Qnew(irep(0))
   new(n): %                   == lper Qnew(nrep(n))
   new(n, s): %                == lper Qnew1(nrep(n), srep s)

   apply(x, i): S	       == elt(x, i)
   qelt(x, i): S               == elt(x, i)
   elt(x:%, i:Integer): S      == sper(Qelt(lrep x, irep(i)))

   qsetelt!(x, i, s): S           == setelt(x, i, s)
   set!(x:%, i:Integer, s:S): S == setelt(x, i, s)
   setelt(x:%, i:Integer, s:S): S == sper Qsetelt(lrep x, irep(i), srep s)

   construct(l: List S): % == never;
