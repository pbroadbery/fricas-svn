--DEPS:  lang Ring
#include "axiom.as"

#pile 

CharacteristicNonZero: Category == Ring with
    charthRoot: % -> Partial %
       ++ charthRoot(x) returns the pth root of x
       ++ where p is the characteristic of the ring.

