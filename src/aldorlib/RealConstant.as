--DEPS: ConvertibleTo init_DoubleFloat init_Float
#include "axiom.as"

#pile
RealConstant: Category ==
  Join(ConvertibleTo DoubleFloat, ConvertibleTo Float)
