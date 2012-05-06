--DEPS: FiniteLinearAggregate IndexedOneDimensionalArray
#include "axiom.as"

IndexedVector(R:Type, mn:Integer): FiniteLinearAggregate R == IndexedOneDimensionalArray(R, mn) add
