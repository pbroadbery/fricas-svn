--DEPS: Vector_FiniteLinearAggregate
#include "axiom.as"
#pile

-- shallowlyMutable added to work around a nasty compiler bug
import from Integer
extend Vector(T: Type): VectorAggregate T with
== IndexedVector(T, 1) add
