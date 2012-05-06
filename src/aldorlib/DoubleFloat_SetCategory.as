--DEPS: init_DoubleFloat SetCategory OutputForm
#include "axiom.as"

#pile
extend DoubleFloat: SetCategory with _
 == add
   (a: %) = (b: %): Boolean == never;
   coerce(a: %): OutputForm == outputForm a; 