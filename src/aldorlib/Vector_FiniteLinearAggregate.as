--DEPS: init_Vector FiniteLinearAggregate IndexedVector_FiniteLinearAggregate
#include "axiom.as"
#pile

-- shallowlyMutable added to work around a nasty compiler bug
import from Integer
extend Vector(T: Type): Join(shallowlyMutable, FiniteLinearAggregate T) with
== IndexedVector(T, 1) add