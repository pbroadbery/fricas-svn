--DEPS: lang Boolean
#include "axiom.as"

import from Boolean;

GcdDom: Category == with { gcd: % -> %;}
PolCat(R: with): Category == with {
   if R has GcdDom then GcdDom
}

-- OK?
--UPolCat3(R: with): Category == with {
--  import from R;
--  if R has GcdDom then {
--     GcdDom;
--  }
--  default {
--    if R has GcdDom then {
--      foo(p: %): % == gcd(p)
--    }
--  }
--}

UPolCat3a(R: with): Category == PolCat R with {
  default { 
    if R has GcdDom then {
      foo(p: %): % == gcd p;
    }
  }
}

---- [L14 C32] #2 (Error) No meaning for identifier `gcd'.
--UPolCat1(R: with): Category == with {
--  import from R;
--  if R has GcdDom then {
--     GcdDom;
--  }
--  if % has GcdDom then {
----     default { foo(p: %): % == gcd(p) }
--  }
--}
--
---- [L26 C32] #2 (Error) No meaning for identifier `gcd'.
--UPolCat2(R: with): Category == with {
--  import from R;
--  if R has GcdDom then {
--     GcdDom;
--  }
--  if R has GcdDom then {
----     default { foo(p: %): % == gcd(p) }
--  }
--}
--
--
---- [L24 C32] #3 (Error) No meaning for identifier `gcd'.
--UPolCat4(R: with): Category == with {
--  import from R;
--  if R has GcdDom then {
--     GcdDom;
--  }
--  if % has GcdDom then {
----     default { foo(p: %): % == gcd(p) }
--  }
--}
--
----[L32 C32] #4 (Error) There are no suitable meanings for the operator `gcd'.
----The following could be suitable if imported:
----  gcd: % -> % from %, if R has GcdDom
--UPolCat5(R: with): Category == with {
--  import from R;
--  if R has GcdDom then {
--     GcdDom;
----     default { foo(p: %): % == gcd(p) }
--  }
--}
--