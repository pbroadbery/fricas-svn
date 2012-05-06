--DEPS:  SemiGroup NonNegativeInteger Partial
#include "axiom.as"

import from Boolean;

Monoid: Category == SemiGroup with {
    --operations
      1: %;                   ++ 1 is the multiplicative identity.
      sample: () -> %;               ++ sample yields a value of type %
      one?: % -> Boolean;                  ++ one?(x) tests if x is equal to 1.
      ^: (%,NonNegativeInteger) -> %;
          ++ x^n returns the repeated product
          ++ of x n times, i.e. exponentiation.
      recip: % -> Partial(%);
          ++ recip(x) tries to compute the multiplicative inverse for x
          ++ or "failed" if it cannot find the inverse (see unitsKnown).
    default {
      import from RepeatedSquaring(%);
      one?(x: %): Boolean == x = 1;
      sample(): % == 1;

      recip(x: %): Partial % == {
       one? x => success(x);
       failed()}
      (x:%) ^ (n:NonNegativeInteger): % == {
         zero? n => 1;
         expt(x,n pretend PositiveInteger)
	 }
}
}

