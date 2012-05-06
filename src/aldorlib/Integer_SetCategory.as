--DEPS:  Integer SetCategory OutputForm
#include "axiom.as"

import from Boolean;

extend Integer: SetCategory with {

} == add {
  coerce(n: %): OutputForm == outputForm(n)
}
