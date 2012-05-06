--DEPS: IndexedFlexibleArray
#include "axiom.as"

#pile
import from Integer

FlexibleArray(S: Type): Exports == Implementation where
  ARRAYMININDEX ==> 1       -- if you want to change this, be my guest
  I ==> Integer
  Exports ==> 
    Join(OneDimensionalArrayAggregate S,ExtensibleLinearAggregate S) with
      flexibleArray : List S -> %
        ++ flexibleArray(l) creates a flexible array from the list of elements l
      physicalLength : % -> NonNegativeInteger
        ++ physicalLength(x) returns the number of elements x can accomodate before growing
      physicalLength!: (%, I) -> %
        ++ physicalLength!(x,n) changes the physical length of x to be n and returns the new array.
      shrinkable: Boolean -> Boolean
        ++ shrinkable(b) sets the shrinkable attribute of flexible arrays to b and returns the previous value
      removeRepeats! : % -> %
        ++ removeRepeats!(u) destructively replaces runs of consequtive
        ++ equal elements of u by single elements.
  Implementation ==> IndexedFlexibleArray(S, ARRAYMININDEX) add
-- Join(OneDimensionalArrayAggregate S, ExtensibleLinearAggregate S)

