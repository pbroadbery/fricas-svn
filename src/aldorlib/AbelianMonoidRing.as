--DEPS: lang Field0 CharacteristicZero CharacteristicNonZero

#include "axiom.as"
import from Boolean;

AbelianMonoidRing(R : Join(SemiRng, AbelianMonoid), E : OrderedAbelianMonoid
                 ) : Category == Join(SemiRng, BiModule(R, R)) with {
    leadingCoefficient: % -> R;
      ++ leadingCoefficient(p) returns the coefficient highest degree term of p.
    leadingMonomial: % -> %;
      ++ leadingMonomial(p) returns the monomial of p with the highest degree.
    degree: % -> E;
      ++ degree(p) returns the maximum of the exponents of the terms of p.
    map: (R -> R, %) -> %;
      ++ map(fn,u) maps function fn onto the coefficients
      ++ of the non-zero monomials of u.
    monomial?: % -> Boolean;
      ++ monomial?(p) tests if p is a single monomial.
    monomial: (R,E) -> %;
      ++ monomial(r,e) makes a term from a coefficient r and an exponent e.
    reductum: % -> %;
         ++ reductum(u) returns u minus its leading monomial
         ++ returns zero if handed the zero element.
    coefficient: (%,E) -> R;
         ++ coefficient(p,e) extracts the coefficient of the monomial with
         ++ exponent e from polynomial p, or returns zero if exponent is not present.
    if R has CancellationAbelianMonoid then CancellationAbelianMonoid;
    if R has SemiRing then SemiRing;
    if R has Ring then Ring;
    if R has Field0 then {
       /: (%,R) -> %;
         ++ p/c divides p by the coefficient c.
    }
    if R has CommutativeRing then {
       CommutativeRing;
       Algebra R;
    }
    if R has CharacteristicZero then CharacteristicZero;
    if R has CharacteristicNonZero then CharacteristicNonZero;
    if R has IntegralDomain then IntegralDomain;
    if R has Algebra Fraction Integer then Algebra Fraction Integer;
 default {
    default x: %;
    monomial? x: Boolean == zero? reductum x;

    map(fn:R -> R, x: %): % == {
       import from R;
          -- this default definition assumes that reductum is cheap
       zero? x => 0;
       r:=fn leadingCoefficient x;
       zero? r => map(fn,reductum x);
       monomial(r, degree x) + map(fn,reductum x)}

    if R has Algebra Fraction Integer then {
      (q:Fraction(Integer)) * (p:%): % == map((x1: R): R+->q*x1, p)}
}
}