--DEPS: Ring init_Matrix init_Vector
#include "axiom.as"

#pile

import from Boolean

LinearlyExplicitRingOver(R:Ring): Category == Ring with
  reducedSystem: Matrix % -> Matrix R
    ++ reducedSystem(A) returns a matrix B such that \spad{A x = 0} and \spad{B x = 0}
    ++ have the same solutions in R.
  reducedSystem: (Matrix %,Vector %) -> Record(mat:Matrix R,vec:Vector R)
    ++ reducedSystem(A, v) returns a matrix B and a vector w such that
    ++ \spad{A x = v} and \spad{B x = w} have the same solutions in R.
