--DEPS: Integer_OrderedRing IntegralDomain IdealElt Integer_OrderedRing
#include "axiom.as"

import from Boolean;
#pile

-- Situation in which '*' from Integer does not get correctly inlined.
II: IntegralDomain with {
    foo: (%, %) -> %;
}
== Integer add {
    import from IdealElt Integer;

    characteristic(): NonNegativeInteger == never;
    (exquo)(a: %, b: %): Partial % == never;
    unitNormal(a: %): Record(unit: %, canonical: %, associate: %) == [-1, a, -1];

    foo(x: %, y: %): % == {
	 s1 := unitNormalize(new(1, 0, x));
	 s2 := unitNormalize(new(0, 1, y));
	 generator s1 + generator s2;
    }
}

