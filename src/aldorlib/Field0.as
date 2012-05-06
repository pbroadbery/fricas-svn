--DEPS: DivisionRing CommutativeRing
#include "axiom.as"

-- Simplest possible field, just a commutative ring.
-- we'll add more fun stuff to it later
Field0: Category == Join(DivisionRing, CommutativeRing) with {
    --operations
      /: (%,%) -> %;
        ++ x/y divides the element x by the element y.
        ++ Error: if y is 0.
}