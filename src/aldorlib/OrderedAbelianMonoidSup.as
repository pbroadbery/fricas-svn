--DEPS: OrderedCancellationAbelianMonoid
#include "axiom.as"

OrderedAbelianMonoidSup: Category == OrderedCancellationAbelianMonoid with {
    --operation
      sup: (%,%) -> %;
        ++ sup(x,y) returns the least element from which both
        ++ x and y can be subtracted.
}