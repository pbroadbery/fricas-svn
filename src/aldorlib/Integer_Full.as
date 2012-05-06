--DEPS: PositiveInteger_Base OrderedAbelianSemiGroup 
--DEPS: Monoid CommutativeStar Integer_IntegralDomain
#include "axiom"

import from System;
import from String;
import from Boolean;
#pile

extend Integer: Join(ConvertibleTo String, _
    Canonical, canonicalsClosed) with
    random   : % -> %
      ++ random(n) returns a random integer from 0 to \spad{n-1}.
 == add
