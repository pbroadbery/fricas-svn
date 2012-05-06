--DEPS: x/Self
#include "axiom.as"

import from Boolean;
#pile

ZZ: Category == Foo with {
 f: () -> ();
 default {
   f(): () == new()
}
}