--DEPS: Monoid unitsKnown RepeatedSquaring init_PositiveInteger
#include "axiom"

import from Boolean;

Group: Category == Join(Monoid, unitsKnown) with {
    --operations
      inv: % -> %;               ++ inv(x) returns the inverse of x.
      /: (%,%) -> %;           ++ x/y is the same as x times the inverse of y.
      ^: (%,Integer) -> %;    ++ x^n returns x raised to the integer power n.
      conjugate: (%,%) -> %;
        ++ conjugate(p,q) computes \spad{inv(q) * p * q}; this is 'right action
        ++ by conjugation'.
      commutator: (%,%) -> %;
        ++ commutator(p,q) computes \spad{inv(p) * inv(q) * p * q}.
 default {
      import from RepeatedSquaring(%);
      default p, q: %;

      (x:%) / (y:%): % == x*inv(y);
      recip(x:%): % == inv(x);
      (x:%) ^ (n:Integer): % == {
         zero? n => 1;
         n<0 => expt(inv(x),(-n) pretend PositiveInteger);
         expt(x,n pretend PositiveInteger)}
      conjugate(p,q): % == inv(q) * p * q;
      commutator(p,q): % == inv(p) * inv(q) * p * q;
}
}