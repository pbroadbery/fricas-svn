--DEPS: List OutputForm x/AC
#include "axiom.as"

#pile
import from Boolean;
import from System;
import from String;

IndexedDirectProductObject(A : SetCategory, S : OrderedSet
                          ) : IDPC(A, S) with _
 == add 
       import from A
    --declarations
       default x,y: %;

    --define
       x = y: Boolean  == never
       -x: % == never

       coerce(x:%):OutputForm == never

       if A has AbelianMonoid then
           0: %  == never
           zero? x: Boolean == (x pretend A) = 0$A
           x + y: % == never

       if A has OrderedAbelianMonoid then
           subtractIfCan(x, y): Partial % ==
	       import from Partial A
               while true repeat
                 0$A + 0$A
               never

