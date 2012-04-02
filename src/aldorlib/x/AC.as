--DEPS: OrderedAbelianMonoid

#include "axiom.as"
import from Boolean;

IDPC(A : SetCategory, S : OrderedSet) : Category
 == with {
      if A has OrderedAbelianMonoid then OrderedAbelianMonoid;
}

