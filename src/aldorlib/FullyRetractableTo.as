--DEPS: RetractableTo Integer_IntegralDomain init_Fraction
#include "axiom.as"

import from Boolean;

FullyRetractableTo(S: Type): Category == RetractableTo(S) with {
    if (S has RetractableTo Integer) then RetractableTo Integer;
    if (S has RetractableTo Fraction Integer) then
              RetractableTo Fraction Integer;
default {
-- these 2 had a test for not(S is Integer) before...
      import from S;
      if (S has RetractableTo Integer) then {   -- induction
        coerce(n:Integer):%  == n::S::%;
        retract(r:%):Integer == retract(retract(r)@S);
      
      retractIfCan(r:%):Partial Integer == {
          default u: Partial S;
          failed?(u:= retractIfCan(r)) => failed();
          retractIfCan(u::S)}
    }

-- these 2 had a test for not(S is Fraction Integer) before...
      if (S has RetractableTo Fraction Integer) then {   -- induction
        coerce(n:Fraction Integer):%  == n::S::%;
        retract(r:%):Fraction(Integer) == retract(retract(r)@S);
    
        retractIfCan(r:%):Partial Fraction Integer == {
	  default u: Partial S;
          failed?(u:=retractIfCan(r)) =>failed();
          retractIfCan(u::S)}
    }
}
}
