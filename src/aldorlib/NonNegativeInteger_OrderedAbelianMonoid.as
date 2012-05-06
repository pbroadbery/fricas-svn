--DEPS: init_NonNegativeInteger OrderedAbelianMonoid CancellationAbelianMonoid
#include "axiom.as"

import from Boolean;

extend NonNegativeInteger: Join(OrderedAbelianMonoid, CancellationAbelianMonoid) with == add {
       coerce(n: %): OutputForm == n::Integer::OutputForm
       subtractIfCan(n: %, m: %): Partial % == if n >= m then success((n-m) pretend %) else failed();
}
