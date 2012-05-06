--DEPS: Integer_SetCategory OrderedRing
#include "axiom.as"

import from Boolean;

extend Integer: OrderedRing with {
}
== add {
       characteristic(): NonNegativeInteger == 0;
}
