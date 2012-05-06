--DEPS: Partial SetCategory
#include "axiom.as"

-- Anyone else think this is a *really* bad idea
StepThrough: Category == SetCategory with {
    --operations
      init: () -> %;
        ++ init() chooses an initial object for stepping.
      nextItem: % -> Partial %;
        ++ nextItem(x) returns the next item, or "failed" if domain is exhausted.
}