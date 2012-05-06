--DEPS: Integer_OrderedRing IntegralDomain IdealElt
#include "axiom.as"

import from Boolean;
#pile

extend Integer: IntegralDomain with {
    foo: % -> %;
}
== add {
    import from IdealElt %;

    characteristic(): NonNegativeInteger == never;
    (exquo)(a: %, b: %): Partial % == never;
    unitNormal(a: %): Record(unit: %, canonical: %, associate: %) == never;

    foo(x: %): %
	 s1 := unitNormalize(new(1, 0, x));
	 (a, b, c) := explode s1;
	 a;
    }
}

