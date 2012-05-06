--DEPS:  EntireRing canonicalUnitNormal Algebra
#include "axiom"

import from Boolean;

IntegralDomain: Category == Join(CommutativeRing, Algebra(%), EntireRing) with {
    --operations
      exquo: (%,%) -> Partial(%);
            ++ exquo(a,b) either returns an element c such that
            ++ \spad{c*b=a} or "failed" if no such element can be found.
      unitNormal: % -> Record(unit:%,canonical:%,associate:%);
            ++ unitNormal(x) tries to choose a canonical element
            ++ from the associate class of x.
            ++ The attribute canonicalUnitNormal, if asserted, means that
            ++ the "canonical" element is the same across all associates of x
            ++ if \spad{unitNormal(x) = [u,c,a]} then
            ++ \spad{u*c = x}, \spad{a*u = 1}.
      unitCanonical: % -> %;
            ++ \spad{unitCanonical(x)} returns \spad{unitNormal(x).canonical}.
      associates?: (%,%) -> Boolean;
        ++ associates?(x,y) tests whether x and y are associates, i.e.
        ++ differ by a unit factor.
      unit?: % -> Boolean;
        ++ unit?(x) tests whether x is a unit, i.e. is invertible.
default {
      -- declaration
      default x,y: %;
      -- definitions
      UCA ==> Record(unit:%,canonical:%,associate:%);
      import from UCA;
      import from Partial %;

--      if not (% has Field) then
--        unitNormal(x): UCA == [1$%,x,1$%]$UCA; -- the non-canonical definition
      unitCanonical(x): % == unitNormal(x).canonical; -- always true

      recip(x): Partial % == if zero? x then failed() else (exquo)(1$%,x);

      unit?(x): Boolean == (failed? recip x => false; true);
      if % has canonicalUnitNormal then {
         associates?(x,y): Boolean ==
           (unitNormal x).canonical = (unitNormal y).canonical;
       }
       else {
         associates?(x,y): Boolean == {
           zero? x => zero? y;
           zero? y => false;
           failed?(x exquo y) => false;
           failed?(y exquo x) => false;
           true
	}
       }
}
}