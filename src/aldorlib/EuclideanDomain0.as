--DEPS: PrincipalIdealDomain0
#include "axiom.as"

import from Boolean;
import from System;
import from String;
#pile

EuclideanDomain0: Category == PrincipalIdealDomain0 
  with
    --operations
    sizeLess?: (%,%) -> Boolean
         ++ sizeLess?(x,y) tests whether x is strictly
         ++ smaller than y with respect to the \spadfunFrom{euclideanSize}{EuclideanDomain}.
    euclideanSize: % -> NonNegativeInteger
         ++ euclideanSize(x) returns the euclidean size of the element x.
         ++ Error: if x is zero.
    divide: (%,%) -> Record(quotient:%,remainder:%)
         ++ divide(x,y) divides x by y producing a record containing a
         ++ \spad{quotient} and \spad{remainder},
         ++ where the remainder is smaller (see \spadfunFrom{sizeLess?}{EuclideanDomain})
         ++ than the divisor y.
    quo : (%,%) -> %
         ++ x quo y is the same as \spad{divide(x,y).quotient}.
         ++ See \spadfunFrom{divide}{EuclideanDomain}.
    rem: (%,%) -> %
         ++ x rem y is the same as \spad{divide(x,y).remainder}.
         ++ See \spadfunFrom{divide}{EuclideanDomain}.
    extendedEuclidean: (%,%) -> Record(coef1:%,coef2:%,generator:%)
                     -- formerly called princIdeal
            ++ extendedEuclidean(x,y) returns a record rec where
            ++ \spad{rec.coef1*x+rec.coef2*y = rec.generator} and
            ++ rec.generator is a gcd of x and y.
            ++ The gcd is unique only
            ++ up to associates if \spadatt{canonicalUnitNormal} is not asserted.
            ++ \spadfun{principalIdeal} provides a version of this operation
            ++ which accepts an arbitrary length list of arguments.
                     -- formerly called expressIdealElt
    extendedEuclidean: (%,%,%) -> Partial(Record(coef1:%,coef2:%))
          ++ extendedEuclidean(x,y,z) either returns a record rec
          ++ where \spad{rec.coef1*x+rec.coef2*y=z} or returns "failed"
          ++ if z cannot be expressed as a linear combination of x and y.
    multiEuclidean: (List %,%) -> Partial List %
          ++ multiEuclidean([f1,...,fn],z) returns a list of coefficients
          ++ \spad{[a1, ..., an]} such that
          ++ \spad{ z / prod fi = sum aj/fj}.
          ++ If no such list of coefficients exists, "failed" is returned.
    default
      import from NonNegativeInteger
      import from Record(quotient: %, remainder: %)
      -- declarations
      default x,y,z: %
      default l: List %
      -- definitions
      sizeLess?(x,y): Boolean ==
            zero? y => false
            zero? x => true
            euclideanSize(x)<euclideanSize(y)

      x quo y: % == divide(x,y).quotient --divide must be user-supplied
      x rem y: % == divide(x,y).remainder
      x exquo y: Partial % ==
         zero? y => failed()
         qr:=divide(x,y)
         zero?(qr.remainder) => success(qr.quotient)
         failed()
      gcd(x,y): % ==                --Euclidean Algorithm
         x:=unitCanonical x
         y:=unitCanonical y
         while not zero? y repeat
            (x,y):= (y,x rem y)
            y:=unitCanonical y             -- this doesn't affect the
                                           -- correctness of Euclid's algorithm,
                                           -- but
                                           -- a) may improve performance
                                           -- b) ensures gcd(x,y)=gcd(y,x)
                                           --    if canonicalUnitNormal
         x
      IdealElt ==> Record(coef1:%,coef2:%,generator:%)
      unitNormalizeIdealElt(s:IdealElt):IdealElt ==
         import from Record(unit:%,canonical:%,associate:%)
         (u,c,a) := explode unitNormal(s.generator)
--         one? a => s
         (a = 1) => s
         [a*s.coef1,a*s.coef2,c]$IdealElt

      extendedEuclidean(x,y): Record(coef1: %, coef2: %, generator: %) ==         --Extended Euclidean Algorithm
         s1:=unitNormalizeIdealElt([1$%,0$%,x]$IdealElt)
         s2:=unitNormalizeIdealElt([0$%,1$%,y]$IdealElt)
         zero? y => s1
         zero? x => s2
         while not zero?(s2.generator) repeat
            qr:= divide(s1.generator, s2.generator)
            s3:=[s1.coef1 - qr.quotient * s2.coef1,
                 s1.coef2 - qr.quotient * s2.coef2, qr.remainder]$IdealElt
            s1:=s2
            s2:=unitNormalizeIdealElt s3
         if not(zero?(s1.coef1)) and not sizeLess?(s1.coef1,y)
           then
              qr:= divide(s1.coef1,y)
              s1.coef1:= qr.remainder
              s1.coef2:= s1.coef2 + qr.quotient * x
              s1 := unitNormalizeIdealElt s1
         s1

      TwoCoefs ==> Record(coef1:%,coef2:%)
      import from TwoCoefs;
      extendedEuclidean(x,y,z): Partial(Record(coef1:%,coef2:%)) ==
         import from Record(coef1:%,coef2:%)
	 import from Record(coef1:%,coef2:%,generator:%)
	 import from Partial %
         zero? z => success([0,0]$TwoCoefs)
         s:= extendedEuclidean(x,y)
         failed?(w:= z exquo s.generator) => failed()
         zero? y =>
            success([ s.coef1 * w::%, s.coef2 * w::%]$TwoCoefs)
         qr:= divide((s.coef1 * w::%), y)
         success([qr.remainder, s.coef2 * w::% + qr.quotient * x]$TwoCoefs)
	 
      principalIdeal l: Record(coef: List %, generator: %) ==
         import from Record(unit:%,canonical:%,associate:%)
	 import from Record(coef1: %, coef2: %, generator: %)
         l = [] => error "empty list passed to principalIdeal"
         rest l = [] =>
              uca:=unitNormal(first l)
              [[uca.unit],uca.canonical]
         rest rest l = [] =>
             u:= extendedEuclidean(first l, second l)
             [[u.coef1, u.coef2], u.generator]
         v:=principalIdeal rest l
         u:= extendedEuclidean(first l,v.generator)
         [cons(u.coef1,[u.coef2*vv for vv in v.coef]),u.generator]
	 
      expressIdealMember(l, z): Partial List % ==
         import from Record(coef:List %,generator:%)
         import from List %
         import from Partial %
         z = 0 => success [0 for v in l]
         pid := principalIdeal l
         failed?(q := z exquo (pid.generator)) => failed()
         success [q::%*v for v in pid.coef]

      multiEuclidean(l,z): Partial List % ==
         import from Integer
	 import from Partial(Record(coef1:%,coef2:%))
         n := #l
         zero? n => error "empty list passed to multiEuclidean"
         n = 1 => success [z]
         l1 := copy l
         l2 := split!(l1, n::Integer quo 2)
         u:= extendedEuclidean(reduce(*, l1), reduce(*,l2), z)
         failed? u => failed()
         v1 := multiEuclidean(l1,coerce(u).coef2)
         failed? v1 => failed();
         v2 := multiEuclidean(l2, coerce(u).coef1)
         failed? v2 => failed()
         success(concat(coerce v1,coerce v2))
