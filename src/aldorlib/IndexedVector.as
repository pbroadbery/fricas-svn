--DEPS: VectorCategory IndexedOneDimensionalArray
#include "axiom.as"

extend IndexedVector(R:Type, mn:Integer):
  VectorCategory R with == IndexedOneDimensionalArray(R, mn) add
