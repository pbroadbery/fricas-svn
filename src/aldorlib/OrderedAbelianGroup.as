--DEPS:  OrderedCancellationAbelianMonoid AbelianGroup
#include "axiom"

import from Boolean;

OrderedAbelianGroup: Category == Join(OrderedCancellationAbelianMonoid, AbelianGroup) with;
