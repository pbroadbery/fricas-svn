--DEPS: lang init_Boolean init_String Integer
#include "axiom.as"

RandomGenerator: with {
  nextInt: % -> Integer
} 
== add {
  nextInt(r: %): Integer == never;
}
