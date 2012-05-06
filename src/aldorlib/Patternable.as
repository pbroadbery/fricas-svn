--DEPS: init_Pattern ConvertibleTo init_Integer init_Float Boolean
#include "axiom.as"

#pile
import from Boolean

Patternable(R:with): Category == with
  if R has ConvertibleTo Pattern Integer then
           ConvertibleTo Pattern Integer
  if R has ConvertibleTo Pattern Float then
           ConvertibleTo Pattern Float
