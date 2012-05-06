--DEPS: UnivariatePolynomialCategory
#include "axiom.as"

#pile
UnivariatePolynomialCategoryFunctions2(R: Ring, PR: UnivariatePolynomialCategory R, 
				       S: Ring,PS: UnivariatePolynomialCategory S): Exports == Impl where
--  default R, S: Ring
--  default PR  : UnivariatePolynomialCategory R
--  default PS  : UnivariatePolynomialCategory S

  Exports ==> with
    map: (R -> S, PR) -> PS
     ++ map(f, p) takes a function f from R to S,
     ++ and applies it to each (non-zero) coefficient of a polynomial p
     ++ over R, getting a new polynomial over S.
     ++ Note: since the map is not applied to zero elements, it may map zero
     ++ to zero.

  Impl ==> add

#if 0
    -- I suspect this is just an optimisation.
    op_of_PS : Symbol := CAR(devaluate(PS)$Lisp)$Lisp

    if op_of_PS = 'UnivariatePolynomial
         or PS is SparseUnivariatePolynomial(S) then

        TermPS ==>  Record(k : Integer, c : S)
        RepPS :=  List TermPS

        map(f, p) ==
            ans : RepPS := []
            while not(p = 0) repeat
                nc := f leadingCoefficient p
                if nc ~= 0 then
                    ans := cons([degree p, nc]$TermPS, ans)
                p := reductum p
            reverse!(ans) pretend PS
    else
#endif
        map(f: R -> S, p: PR): PS ==
            ans:PS := 0
            while not(p = 0) repeat
                ans := ans + monomial(f leadingCoefficient p, degree p)
                p   := reductum p
            ans
