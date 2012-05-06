--DEPS: SemiRng AbelianMonoid IndexedDirectProductCategory BiModule
--DEPS: SemiRing RetractableTo CommutativeRing Module

#include "axiom.as"

#pile
import from Boolean

FreeModuleCategory(R: Join(SemiRng, AbelianMonoid), S: OrderedSet):Category == 
 Join(BiModule(R,R), IndexedDirectProductCategory(R,S)) 
  with
        if R has SemiRing then RetractableTo S
        *                : (R, S) -> %
          ++ \spad{r*b} returns the product of \spad{r} by \spad{b}.
        *:(S,R) -> %
          ++ \spad{s*r} returns the product \spad{r*s}
          ++ used by \spadtype{XRecursivePolynomial}
        coefficients       : % -> List R
          ++ \spad{coefficients(x)} returns the list of coefficients of \spad{x}.
        support            : % -> List S
          ++ \spad{support(x)} returns the list of basis elements with nonzero coefficients.
        monomials          : % -> List %
          ++ \spad{monomials(x)} returns the list of \spad{r_i*b_i}
          ++ whose sum is \spad{x}.
        numberOfMonomials  : % -> NonNegativeInteger
          ++ \spad{numberOfMonomials(x)} returns the number of monomials of \spad{x}.
        monomial?: % -> Boolean
          ++ \spad{monomial?(x)} returns true if \spad{x} contains a single
          ++ monomial.
        leadingMonomial    : % -> S
          ++ \spad{leadingMonomial(x)} returns the first element from \spad{S}
          ++ which appears in \spad{listOfTerms(x)}.
        leadingCoefficient : % -> R
          ++ \spad{leadingCoefficient(x)} returns the first coefficient
          ++ which appears in \spad{listOfTerms(x)}.
        monom : (S, R) -> %
          ++ \spad{monom(s,r)} returns the product of the basis element \spad{s} by the coefficient \spad{r}.
        coefficient :(%,S) -> R
          ++ \spad{coefficient(x,s)} returns the coefficient of the basis element s
        -- attributs
        if R has CommutativeRing then
             Module(R)
             linearExtend:(S->R,%)->R
               ++ \spad{linearExtend:(f,x)} returns the linear extension
               ++ of a map defined on the basis applied to a linear combination
        if R has Comparable then Comparable

        default 
	  import from S
	  import from R
          if R has Comparable then
	     bar: String -> String
             smaller?(p : %, q : %) : Boolean == 
              while true repeat
                  zero?(q) => return false
                  zero?(p) => return true
                  if leadingMonomial(p) = leadingMonomial(q) then
                      if leadingCoefficient(p) = leadingCoefficient(q) then
                          p := reductum p
                          q := reductum q
                      else
                          return smaller?(leadingCoefficient(p),
                                          leadingCoefficient(q))
                  else
                      return leadingMonomial(p) < leadingMonomial(q)
	      never

