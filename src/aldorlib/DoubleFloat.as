--DEPS: init_DoubleFloat Boolean
#include "axiom.as"

#pile
extend DoubleFloat: 
 with 
   =: (%, %) -> Boolean
   float: Literal -> %
 == add
   import from Machine
   Rep ==> DFlo;
   (a: %) = (b: %): Boolean == never
   float(l: Literal): % == per convert(l pretend Arr)
