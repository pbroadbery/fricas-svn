--DEPS: Ring LinearlyExplicitRingOver Integer_OrderedRing init_Matrix init_Vector
#include "axiom.as"

import from Boolean;

FullyLinearlyExplicitRingOver(R:Ring):Category == LinearlyExplicitRingOver R 
 with {
    if (R has LinearlyExplicitRingOver Integer) then
            LinearlyExplicitRingOver Integer;
    default {
--  if not(R is Integer) then
     import from R;
     import from Record(mat:Matrix Integer, vec:Vector Integer);
     import from Record(mat:Matrix R, vec:Vector R);

     if (R has LinearlyExplicitRingOver Integer) then {
      reducedSystem(m:Matrix %):Matrix(Integer) ==
        reducedSystem(reducedSystem(m)@Matrix(R));

      reducedSystem(m:Matrix %, v:Vector %):
        Record(mat:Matrix(Integer), vec:Vector(Integer)) == {
          rec := reducedSystem(m, v)@Record(mat:Matrix R, vec:Vector R);
          reducedSystem(rec.mat, rec.vec);}
     }
  }
}