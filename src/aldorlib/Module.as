#include "axiom"

import from Boolean;

Module(R:CommutativeRing): Category == BiModule(R,R) with {
  default {
--    if not(R = %) then (x:%)* (r:R): % == r*x
}
}
