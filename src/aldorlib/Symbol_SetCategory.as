--DEPS: init_Symbol SetCategory OutputForm
#include "axiom.as"

import from Boolean;
extend Symbol: SetCategory with  {

}
== add {
   (a: %) = (b: %): Boolean == never;
   coerce(a: %): OutputForm == outputForm a;
}

