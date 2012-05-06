--DEPS: String SetCategory XLisp OutputForm
#include "axiom.as"
#pile

extend String: SetCategory with _
  == add
      Rep ==> XLisp;
      import from Rep;
      (a: %) = (b: %): Boolean == EQUAL(rep(a), rep(b))
      coerce(a: %): OutputForm == outputForm a