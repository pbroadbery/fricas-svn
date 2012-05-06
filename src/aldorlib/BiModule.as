#include "axiom"

import from Boolean;

BiModule(R : SemiRng, S : SemiRng) : Category ==
  Join(LeftModule(R), RightModule(S)) with;
