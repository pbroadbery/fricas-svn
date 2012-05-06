--DEPS: PatternMatchable Integer_SetCategory Float_SetCategory
#include "axiom.as"

#pile

FullyPatternMatchable(R:with): Category == with
  if R has PatternMatchable Integer then PatternMatchable Integer
  if R has PatternMatchable Float   then PatternMatchable Float

