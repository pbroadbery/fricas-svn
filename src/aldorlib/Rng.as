--DEPS:  AbelianGroup NonNegativeInteger
#include "axiom.as"

import from Boolean;

Rng: Category == AbelianGroup with { -- & SemiRng
     0: %;
}
