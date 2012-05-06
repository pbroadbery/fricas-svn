--DEPS: init_NonNegativeInteger OrderedAbelianMonoidSup CancellationAbelianMonoid NonNegativeInteger OutputForm

#include "axiom.as"

import from Boolean;

extend NonNegativeInteger: OrderedAbelianMonoidSup with == add {
       coerce(n: %): OutputForm == outputForm(n::Integer);
       subtractIfCan(n: %, m: %): Partial % == if n >= m then success((n-m) pretend %) else failed();
       sup(x: %, y: %): % == max(x, y);
}
