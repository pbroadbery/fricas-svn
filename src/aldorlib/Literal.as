--DEPS: lang Basic
#include "axiom.as"

extend Literal: with {
  coerce: % -> BasicArray;
}
== add {
  Rep == BasicArray;
  coerce(x: %): BasicArray == rep x;
}