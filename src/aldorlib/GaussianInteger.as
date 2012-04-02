--DEPS: IntegralDomain Symbol OutputForm Integer_IntegralDomain
#include "axiom.as"

import from String;
import from System;

-- Simple definition.. Just enough to supply us with example fodder
GaussianInteger: IntegralDomain with
== add {
   Rep ==> Record(realPart: Integer, imagPart: Integer);
   import from Rep;
   import from Integer;
   import from Symbol;

   real(a: %): Integer == rep(a).realPart;
   imag(a: %): Integer == rep(a).imagPart;
   
   new(realPart: Integer, imagPart: Integer): % == per [realPart, imagPart];

   0: % == new(0, 0);
   1: % == new(1, 0);

   (a: %) = (b: %): Boolean == real(a) = real(b) and imag(a) = imag(b);
   (a: %) + (b: %): % == new(real a + real b, imag a + imag b);
   (a: %) * (b: %): % == new(real a*real b - imag a * imag b, real a * imag b + imag a * real b);
   -(a: %): % == new(-real a, -imag a);

   coerce(a: %): OutputForm == coerce(real a) + coerce(imag a) * outputForm(#"i");

   characteristic(): NonNegativeInteger == 0;

   (exquo)(a: %, b: %): Partial % == {
      import from Partial Integer;
      zero? b => error "Division by zero";
      normSquared := real b * real b + imag b * imag b;
      tmp := real a * real b + imag a * imag b;
      realPart := tmp exquo normSquared;
      failed? realPart => failed();
      imagPart := (real b * realPart::Integer - real a) exquo imag b;
      failed? imagPart => failed();
      success(new(realPart::Integer, imagPart::Integer));
   }
   
   unitNormal(x: %): Record(unit: %, canonical: %, associate: %) == {
      real x >= 0 and imag x >= 0 => [1, x, 1];
      real x >= 0 and imag x < 0  => [new(0, 1), new(0, -1) * x, new(0, -1)];
      real x < 0 and imag x >= 0  => [new(0, -1), new(0, 1) * x, new(0, 1)];
      real x < 0 and imag x < 0   => [new(-1, 0), new(-1, 0) * x, new(-1, 0)];
      never;
   }

}
