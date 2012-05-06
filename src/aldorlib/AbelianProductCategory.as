--DEPS: AbelianMonoid CancellationAbelianMonoid AbelianGroup
#include "axiom.as"

import from Boolean;

AbelianProductCategory(A : with) : Category == with {
    if A has AbelianMonoid then AbelianMonoid;
    if A has CancellationAbelianMonoid then CancellationAbelianMonoid;
    if A has AbelianGroup then AbelianGroup;
}