--DEPS: EntireRing Algebra Fraction_CommutativeRing Integer_IntegralDomain

#include "axiom.as"

import from Boolean;
import from String;
import from System;

DivisionRing: Category == 
 Join(EntireRing, Algebra Fraction Integer) with {
      ^: (%,Integer) -> %;
          ++ x^n returns x raised to the integer power n.
      inv : % -> %;
          ++ inv x returns the multiplicative inverse of x.
          ++ Error: if x is 0.
-- Q-algebra is a lie, should be conditional on characteristic 0,
-- but knownInfo cannot handle the following commented
--    if % has CharacteristicZero then Algebra Fraction Integer
 default {
      default n: Integer;
      default x: %;
      import from RepeatedSquaring(%);
      x ^ n: % == {
         zero? n => 1;
         zero? x => {
            n<0 => error "division by zero";
            x}
         n<0 =>
            expt(inv x,(-n) pretend PositiveInteger);
         expt(x,n pretend PositiveInteger);}
--    if % has CharacteristicZero() then
      (q:Fraction(Integer)) * (x:%): % == numer(q) * inv(denom(q)::%) * x;

}
}