#include "axiom.as"

import from Boolean;

CommutativeRing:Category == Join(Ring, BiModule(%,%), CommutativeStar) with;
