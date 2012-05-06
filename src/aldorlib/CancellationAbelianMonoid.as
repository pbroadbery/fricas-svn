--DEPS:  AbelianMonoid Partial
#include "axiom.as"

import from Boolean;

CancellationAbelianMonoid: Category == AbelianMonoid with {
    --operations
      subtractIfCan: (%,%) -> Partial %;
}

