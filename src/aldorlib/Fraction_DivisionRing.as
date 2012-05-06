--DEPS: Fraction_CommutativeRing DivisionRing Integer_IntegralDomain Field0

#include "axiom.as"

extend Fraction(S: IntegralDomain): Field0 with {
}
== add {
   import from S;
   FI ==> Fraction Integer;
   (x: %) * (a: Fraction Integer): % == a * x;
   inv(a: %): % == denom a/numer a;
   (a: %) / (b: %): % == a * inv b;
}