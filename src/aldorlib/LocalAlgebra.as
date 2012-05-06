--DEPS: Localize Algebra CommutativeRing OrderedRing
#include "axiom.as"

import from Boolean;

-- Note that this has its arguments reversed from the Axiom code.
-- FIXME: That's strictly a compiler bug, but it can wait until something
-- more frequently used shows up.

LocalAlgebra(R: CommutativeRing, A: Algebra R): Algebra R with {
          if A has OrderedRing then OrderedRing;
          / : (%,R) -> %;
            ++ x / d divides the element x by d.
          / : (A,R) -> %;
            ++ a / d divides the element \spad{a} by d.
          numer: % -> A;
            ++ numer x returns the numerator of x.
          denom: % -> R;
            ++ denom x returns the denominator of x.
}
 == Localize(A, R) add {
        import from A, R;
        1: % == 1$A / 1$R;
        --(x:%) * (y:%): % == per (numer(rep(x)) * numer(rep(y))) / (denom(rep(x)) * denom(rep(y)));
        (x:%) * (y:%): % == (numer x * numer y)/(denom x * denom y);
        characteristic(): NonNegativeInteger == characteristic()$A;
	sample: % == 1;
}
