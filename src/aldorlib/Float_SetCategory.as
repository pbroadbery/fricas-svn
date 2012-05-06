--DEPS: init_Float SetCategory
#include "axiom.as"

#pile
extend Float: SetCategory with 
== add 
   (a: %) = (b: %): Boolean == never
   coerce(a: %): OutputForm == never
