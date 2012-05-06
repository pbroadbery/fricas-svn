--DEPS:  OrderedAbelianMonoid CancellationAbelianMonoid
#include "axiom"

import from Boolean;

OrderedCancellationAbelianMonoid: Category == Join(OrderedAbelianMonoid, CancellationAbelianMonoid) with;
