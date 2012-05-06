--DEPS: IntegralDomain
#include "axiom.as"

IdealElt(I: IntegralDomain): with {
   new: (I, I, I) -> %;
   unitNormalize: % -> %;
   next: (%, %, I, I) -> %;
   explode: % -> (I, I, I);
   generator: % -> I;
   coef1: % -> I;
   coef2: % -> I;
}
== add {
   Rep ==> Record(coef1: I, coef2: I, generator: I);
   import from Record(unit: I, canonical: I, associate: I);
   import from Rep;
   default a, b, c: I;

   new(a, b, c): % == per[a, b, c];

   unitNormalize(elt: %): % == {
       (u, c, a) := explode unitNormal(generator elt);
       a = 1 => elt;
       new(a * coef1 elt, a*coef2 elt, c);
   }

   next(s1: %, s2: %, q: I, r: I): % == {
      unitNormalize new(coef1 s1 - q * coef1 s2, 
          	        coef2 s1 - q * coef2 s2, r);
   }

   explode(s: %): (I, I, I) == explode rep s;
   
   generator(elt: %): I == rep(elt).generator;
   coef1(elt: %): I == rep(elt).coef1;
   coef2(elt: %): I == rep(elt).coef2;
}

