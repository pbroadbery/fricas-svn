--DEPS: VectorCategory IndexedVector 
#include "axiom.as"
#pile
import from Boolean

VECTORMININDEX ==> 1       -- if you want to change this, be my guest
import from Integer;

extend Vector(R:Type): VectorCategory R with
   vector: List R -> %
     ++ vector(l) converts the list l to a vector.
   bracket: Tuple R -> %;
   bracket: Generator R -> %;
   apply: (%, Integer) -> R
 == IndexedVector(R, VECTORMININDEX) add
     default x: %;
     default i: Integer
     default s: R

     -- qelt and qsetelt! are logically unnecessary, but good for
     -- performance
     Qelt1 ==> QAREF1O$Lisp
     Qsetelt1 ==> QSETAREF1O$Lisp

     --qelt(x, i) == Qelt1(x, i, VECTORMININDEX@Integer)
     --qsetelt!(x, i, s) == Qsetelt1(x, i, s, VECTORMININDEX@Integer)
     qelt(x, i): R == elt(x, i)
     qsetelt!(x, i, s): R == setelt(x, i, s)

     vector(l: List R): % == construct l
     if R has ConvertibleTo InputForm then
       convert(x:%):InputForm == never

     -- ? In VectorCategory?
     [a: Tuple R]: % == never;
     [a: Generator R]: % == never;
     apply(x: %, i: Integer): R == never