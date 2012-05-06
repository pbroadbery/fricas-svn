--DEPS: Integer_OrderedRing IntegralDomain IdealElt
#include "axiom.as"

import from Boolean;
#pile

extend Integer: IntegralDomain with {
    extendedEuclidean: (%, %) -> (%, %, %)
}
== add {
    import from IdealElt %;

    characteristic(): NonNegativeInteger == 0;
    (exquo)(a: %, b: %): Partial % == {
    	    (q, r) := divide(a, b);
	    if zero? r then success(q)
	    else failed();
	    
    }
    unitNormal(a: %): Record(unit: %, canonical: %, associate: %) == if a > 0 then [1, a, 1] else [-1, a, -1];

    extendedEuclidean(x: %, y: %): (%, %, %) == {
	 s1 := unitNormalize(new(1, 0, x));
	 s2 := unitNormalize(new(0, 1, y));
         zero? y => explode s1;
         zero? x => explode s2;
         while not zero?(generator s2) repeat {
            (q, r) := divide(generator s1, generator s2);
	    s3 := next(s1, s2, q, r);
            s1:=s2;
            s2:=s3;
         }
         if not(zero?(coef1 s1)) and not(coef1 s1 < y) then {
              (q, r) := divide(coef1 s1, y);
	      s1 := new(r, coef2 s1 + q * x, generator s1);
              s1 := unitNormalize s1;
	   }
         explode s1
	}

}

