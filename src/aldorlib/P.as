--DEPS: SemiRng AbelianMonoid Monoid
#include "axiom.as"

import from Boolean;

P(R: Join(SemiRng, AbelianMonoid)): with { foo: () -> R } == add { if R has Monoid then foo(): R == 1}
