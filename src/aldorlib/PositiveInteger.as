--DEPS: PositiveInteger_Base OrderedAbelianSemiGroup 
--DEPS: Monoid CommutativeStar Integer_EuclideanDomain
#include "axiom"

import from System;
import from String;
import from Boolean;
#pile

extend PositiveInteger: Join(OrderedAbelianSemiGroup, Monoid, CommutativeStar) with
            gcd: (%,%) -> %
              ++ gcd(a,b) computes the greatest common divisor of two
              ++ positive integers \spad{a} and b.
	    random: () -> %
 == add
  Rep ==> Integer
  import from Rep

  (=)(a: %, b: %): Boolean == rep(a) = rep(b)
  coerce(a: %): OutputForm == coerce rep a
  (+)(a: %, b: %) : % == per(rep(a)+rep(b))
  (*)(a: %, b: %) : % == per(rep(a)*rep(b))
  gcd(a: %, b: %) : % == per(gcd(rep(a), rep(b)))

  random(): % == never
