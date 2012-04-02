--DEPS: Integer_OrderedRing IntegralDomain IdealElt
#include "axiom.as"

import from Boolean;
#pile

-- Situation in which '*' from Integer does not get correctly inlined.
extend Integer: IntegralDomain with {
    foo: (%, %) -> %;
}
== add {
    import from IdealElt %;

    characteristic(): NonNegativeInteger == never;
    (exquo)(a: %, b: %): Partial % == never;
    unitNormal(a: %): Record(unit: %, canonical: %, associate: %) == [-1, a, -1];

    Rep ==> BInt;
    import from Machine;
    (a: %) * (b: %): % == per(rep a * rep b);

    foo(x: %, y: %): % == {
	 s1 := unitNormalize(new(1, 0, x));
	 s2 := unitNormalize(new(0, 1, y));
	 (a, b) := divide(generator s1, generator s2);
	 a+b
    }
}

