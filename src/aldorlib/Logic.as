--DEPS: BasicType
#include "axiom.as"

#pile
Logic: Category == BasicType with
       ~:        % -> %
        ++ ~(x) returns the logical complement of x.
       /\:       (%, %) -> %
        ++ \spadignore { /\ }returns the logical `meet', e.g. `and'.
       \/:       (%, %) -> %
        ++ \spadignore{ \/ } returns the logical `join', e.g. `or'.
       default
          (\/)(x: %,y: %): % == ~(  (~(x) /\ ~(y)))

