--DEPS: OrderedAbelianMonoid SemiRng AbelianMonoidRing FullyRetractableTo Segment_SegmentCategory
#include "axiom.as"

import from Boolean;
import from System;
import from String;

FiniteAbelianMonoidRing(R : Join(SemiRng, AbelianMonoid),
                        E : OrderedAbelianMonoid) : Category == 
   Join(AbelianMonoidRing(R,E),FullyRetractableTo R) with {
    ground?: % -> Boolean;
      ++ ground?(p) tests if polynomial p is a member of the coefficient ring.
                    -- can't be defined earlier, since a power series
                    -- might not know if there were other terms or not
    ground: % -> R;
      ++ ground(p) retracts polynomial p to the coefficient ring.
    coefficients: % -> List R;
      ++ coefficients(p) gives the list of non-zero coefficients of polynomial p.
    numberOfMonomials: % -> NonNegativeInteger;
      ++ numberOfMonomials(p) gives the number of non-zero monomials in polynomial p.
    minimumDegree: % -> E;
      ++ minimumDegree(p) gives the least exponent of a non-zero term of polynomial p.
      ++ Error: if applied to 0.
    mapExponents: (E -> E, %) -> %;
      ++ mapExponents(fn,u) maps function fn onto the exponents
      ++ of the non-zero monomials of polynomial u.
    pomopo!: (%,R,E,%) -> %;
         ++ \spad{pomopo!(p1,r,e,p2)} returns \spad{p1 + monomial(e,r) * p2}
         ++ and may use \spad{p1} as workspace. The constaant \spad{r} is
         ++ assumed to be nonzero.
    if R has CommutativeRing then {
       binomThmExpt: (%,%,NonNegativeInteger) -> %;
         ++ \spad{binomThmExpt(p,q,n)} returns \spad{(x+y)^n}
         ++ by means of the binomial theorem trick.
    }
    if R has IntegralDomain then {
       exquo: (%,R) -> Partial %;
       ++ exquo(p,r) returns the exact quotient of polynomial p by r, or "failed"
       ++ if none exists.
    }
    if R has GcdDomain0 then {
       content: % -> R;
         ++ content(p) gives the gcd of the coefficients of polynomial p.
       primitivePart: % -> %;
         ++ primitivePart(p) returns the unit normalized form of polynomial p
         ++ divided by the content of p.
    }
  default {
    import from Segment Integer;
    default x, y: %;
    default r: R;
    default i: NonNegativeInteger;
    default nn: NonNegativeInteger;

    pomopo!(p1: %,r: R,e: E,p2: %): % == p1 + r * mapExponents((x1: E): E+-> x1+e, p2);

    if R has CommutativeRing then {
       binomThmExpt(x,y,nn): % == {
               nn = 0 => 1$%;
               default ans,xn,yn: %;
               default bincoef: Integer;
               powl: List(%):= [x];
               for n in 2..nn::Integer repeat powl:= cons(x * powl.first, powl); -- NB was [x * powl.first, :powl]
               yn:=y; ans:=powl.first; i:=1; bincoef:=nn::Integer;
               for xn in powl.rest repeat {
                  ans:= bincoef * xn * yn + ans;
                  bincoef:= (nn-i) * bincoef quo (i+1)::Integer;  i:= i+1;
                  -- last I and BINCOEF unused
                  yn:= y * yn}
               ans + yn}
    }
    ground? x: Boolean == {
      import from Partial R;
      failed?(retractIfCan(x)@Partial R) => false;
      true}
    ground x: R == retract(x)@R;
    mapExponents (fn:E -> E, x: %): % == {
         -- this default definition assumes that reductum is cheap
       zero? x => 0;
       monomial(leadingCoefficient x,fn degree x)+mapExponents(fn,reductum x)}
    coefficients x: List R == {
      zero? x => empty();
      concat(leadingCoefficient x, coefficients reductum x)}

    if R has Field0 then
       x/r: % == map((x1: R): R+->x1/r,x);
    if R has IntegralDomain then {
       (x : %) exquo (r : R): Partial % == {
          import from Partial R;
          zero? r => error "Division by 0";
          zero? x => success(0);
          ans : % := 0;
          while not zero? x repeat {
              t := leadingCoefficient x exquo r;
              failed?(t) => return failed();
              ans := ans + monomial(t::R, degree x);
              x := reductum x;}
          success(ans)}
    }
    if R has GcdDomain0 then {
       content x: R == {      -- this assumes  reductum is cheap
          zero? x => 0;
          r:=leadingCoefficient x;
          x:=reductum x;
--          while not zero? x and not one? r repeat
          while not zero? x and not (r = 1) repeat {
            r:=gcd(r,leadingCoefficient x);
            x:=reductum x}
          r}
       primitivePart x: % == {
          import from Partial %;
          zero? x => x;
          c := content x;
	  pp: % := (x exquo c)::%;
	  u : % -> % := unitCanonical;
          unitCanonical(pp)}
     }
  }
}