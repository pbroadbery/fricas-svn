--DEPS:  AbelianGroup NonNegativeInteger
#include "axiom.as"

import from Boolean;

Rng: Category == AbelianGroup with { -- & SemiRng
     foo: Integer -> %;
     0: %;
     default { foo(n: Integer): % == { n * 0 }}
}
