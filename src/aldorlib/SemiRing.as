--DEPS:  SemiRng AbelianMonoid Monoid
#include "axiom.as"

import from Boolean;

SemiRing: Category == Join(SemiRng, AbelianMonoid, Monoid) with;