--DEPS: String SetCategory OutputForm
#include "axiom.as"
#pile

extend String: SetCategory with _
  == add
      coerce(a: %): OutputForm == outputForm a