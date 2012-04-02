--DEPS: init_Fraction CommutativeRing GcdDomain0 Partial LocalAlgebra OutputForm

#include "axiom.as"
import from Boolean;
import from System;
import from String;

-- Ideally, I'd like to add DivisionRing in here as well,
-- but division ring is delared to be a Algebra Fraction Integer,
-- which would imply a circular dependency.

extend Fraction(S: IntegralDomain): CommutativeRing with {
       numer: % -> S;
       denom: % -> S;
       /: (S, S) -> %;
       coerce: S -> %;
}
== LocalAlgebra(S, S) add {
   -- PAB: Would prefer Rep == LocalAlgebra(S, S)
    Rep == Record(num:S, den:S);
    import from Rep;
    default x, y, g, z: %;    
    1: % == per [1, 1];
    0: % == per [0, 1];

      x + y: %  == {
        zero? y => x;
        zero? x => y;
        z := per [rep(x).den,rep(y).den];
        d := cancelGcd z;
        g := per [rep(z).den * rep(x).num + rep(z).num * rep(y).num, d];
        cancelGcd g;
        rep(g).den := rep(g).den * rep(z).num * rep(z).den;
        normalize g}

    sample(): % == 1;
    characteristic(): NonNegativeInteger == characteristic()$S;
    
    (a: %) = (b: %): Boolean == rep(a).num = rep(b).num and rep(a).den = rep(b).den;

    -(x: %): % == per [-rep(x).num, rep(x).den];

    coerce(x:%):OutputForm == {
--        one?(xd:=x.den) => (x.num)::OutputForm;
        ((xd := rep(x).den) = 1) => (rep(x).num)::OutputForm;
        (rep(x).num)::OutputForm / (xd::OutputForm);
    }

    coerce(s: S): % == per [s, 1];

--    if S has GcdDomain0 then {
    x - y: %  == {
        zero? y => x;
        z := per [rep(x).den, rep(y).den];
        d := cancelGcd z;
        g := per [rep(z).den * rep(z).num - rep(z).num * rep(y).num, d];
        cancelGcd g;
        rep(g).den := rep(g).den * rep(z).num * rep(z).den;
        normalize g}

      (x:%) * (y:%): %  =={
        zero? x or zero? y => 0;
--        one? x => y;
        (x = 1) => y;
--        one? y => x;
        (y = 1) => x;
        (x, y) := (per [rep(x).num, rep(y).den], per [rep(y).num, rep(x).den]);
        cancelGcd x; cancelGcd y;
        normalize per [rep(x).num * rep(y).num, rep(x).den * rep(y).den]}

      local cancelGcd x: S == {
        ((rep(x).den) = 1) => rep(x).den;
        if S has GcdDomain0 then {
        d := gcd(rep(x).num, rep(x).den);
        xn: Partial S := rep(x).num exquo d;
        failed?(xn) =>
          error "gcd not gcd in QF cancelGcd (numerator)";

        xd := rep(x).den exquo d;
        failed?(xd) =>
          error "gcd not gcd in QF cancelGcd (denominator)";
        rep(x).num := xn :: S;
        rep(x).den := xd :: S;
        d}
	else return 1}

      local normalize y: % == {
        UCA ==> Record(unit:S,canonical:S,associate:S);
	import from UCA;
        import from S;
        repy := rep(y);
        zero?(repy.num) => 0;
--        one?(repy.den) => repy;
        ((repy.den) = 1) => y;
        uca := unitNormal(repy.den);
        zero?(repy.den := uca.canonical) => error "division by zero";
        repy.num := repy.num * uca.associate;
        y}

      if S has canonicalUnitNormal then {
        x = y: Boolean == (rep(x).num = rep(y).num) and (rep(x).den = rep(y).den);
    --x / dd == (cancelGcd (z:=[x.num,dd*x.den]); normalize z)

--        one? x == one? (rep(x).num) and one? (x.den)
        one? x: Boolean == ((rep(x).num) = 1) and ((rep(x).den) = 1);
                  -- again assuming canonical nature of representation
     }
     else {
      (nn:S)/(dd:S): % == if zero? dd then error "division by zero" else per [nn,dd];

      recip x: Partial % == {
        zero?(rep(x).num) => failed();
        success(per[rep(x).den, rep(x).num])}
    }

--}
}
