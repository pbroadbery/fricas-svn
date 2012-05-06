--DEPS: init_Vector FiniteLinearAggregate IndexedVector_FiniteLinearAggregate
#include "axiom.as"
#pile

import from Integer
extend Vector(T: Type): FiniteLinearAggregate T with
== IndexedVector(T, 1) add