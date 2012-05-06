--DEPS: OneDimensionalArrayAggregate UniversalSegment PrimitiveArray_Base
#include "axiom.as"

#pile

extend PrimitiveArray(S:Type): OneDimensionalArrayAggregate S == add
   default x: %
   default s: S
   import from UniversalSegment Integer
   fill!(x, s): %       == (for i in minIndex x..maxIndex x repeat x.i := s; x)


