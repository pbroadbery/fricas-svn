--DEPS: FreeModuleCategory IndexedDirectProductObject noZeroDivisors NonNegativeInteger
#include "axiom.as"

#pile
import from Boolean
import from System
import from String

FreeModule(R : Join(SemiRng, AbelianMonoid), S : OrderedSet) :
        Join(BiModule(R,R),FreeModuleCategory(R,S)) with
    if R has CommutativeRing then Module(R)
 == IndexedDirectProductObject(R, S) add
    --representations
       Term ==>  Record(k:S,c:R)
       Rep ==  List Term
       import from Rep
       import from Term
       import from IndexedDirectProductObject(R, S)
    --declarations
       default x,y: %
       default r: R
       default n: Integer
       default f: R -> R
       default s: S
       default lt: List Term

       local null(x: %): Boolean == null rep(x)
       local empty?(x: %): Boolean == null rep(x)
       local apply(x: %, zz: 'first'): Term == rep(x).first
       local apply(x: %, zz: 'rest'): % == per(rep(x).rest)
   --define
       r__one : R :=
           R has Monoid => 1
           0

       if R has noZeroDivisors then
         r * x: %  ==
             zero? r => 0
             (r = r__one) => x
           --map(x+->r*x1,x)
             per [[u.k,r*u.c] for u in rep x ]
       else
         r * x: %  ==
             zero? r => 0
             (r = r__one) => x
           --map(x1+->r*x1,x)
             per [[u.k,a] for u in rep x | (a:=r*u.c) ~= 0$R]

       if R has noZeroDivisors then
         x * r: %  ==
             zero? r => 0
             (r = r__one) => x
           --map(x1+->r*x1,x)
             per [[u.k,u.c*r] for u in rep x ]
       else
         x * r: %  ==
             zero? r => 0
             (r = r__one) => x
           --map(x1+->r*x1,x)
             per [[u.k,a] for u in rep x | (a:=u.c*r) ~= 0$R]

       r * s: % ==
         r = 0 => 0
         per [[s,r]$Term]

       s * r: % ==
         r = 0 => 0
         per [[s,r]$Term]

       if R has Monoid then
           coerce(x) : OutputForm == never

       leadingMonomial x: S == x.first.k

       support x: List S == [t.k for t in rep x]

       coefficients x: List R == [t.c for t in rep x]

       monomials x: List %  == [ monom (t.k, t.c) for t in rep x]

       if R has SemiRing then
           import from NonNegativeInteger
           retractIfCan x: Partial S ==
               numberOfMonomials(x) ~= 1 => failed()
               x.first.c = 1 => success(x.first.k)
               failed()

           retract x: S ==
	       import from Partial S
               failed?(rr := retractIfCan x) =>
                   error "FM1.retract impossible"
               rr :: S

           coerce(s : S):% == per [[s, 1$R]]

-- the following is to be replaced by monomial(r,b) everywhere
       monom(b: S,r):% == per [[b,r]$Term]

       coefficient(x,s): R ==
         null x => 0$R
         x.first.k > s => coefficient(x.rest,s)
         x.first.k = s => x.first.c
         0$R

       monomial? x: Boolean ==
         numberOfMonomials x = 1

       listOfTerms(x): List Term ==
--          (x::Rep)
--          coerce(x)@Rep
         x pretend Rep

       numberOfMonomials x: NonNegativeInteger == # (listOfTerms x)

       if R has CommutativeRing then
           default f:S->R
           default x:%
           default t:Term
           linearExtend(f,x): R ==
               zero? x => 0
               res:R:= 0
               for t in listOfTerms x repeat
                   res := res + (t c)*f(t k)
               res

