--DEPS: SparseUnivariatePolynomial_UnivariatePolynomialCategory PolynomialFactorizationExplicit0 
--DEPS: Factored_Base Matrix_MatrixCategory LinearPolynomialEquationByFractions
--DEPS: Field UnivariatePolynomialCategoryFunctions2 Fraction_QuotientFieldCategory1
#include "axiom.as"
#pile

PolynomialFactorizationExplicit: Category == Definition where
  P ==> SparseUnivariatePolynomial %
  Definition ==>
    PolynomialFactorizationExplicit0 with
	default Defaults
--  Exports ==>
--    -- operations
  Defaults ==>
        default f, g: P
	default lf: List P
	import from Integer

        gcdPolynomial(f,g): P ==
	   import from Partial P
           zero? f => g
           zero? g => f
           cf:=content f
           if not one? cf then f:=(f exquo cf)::P
           cg:=content g
           if not one? cg then g:=(g exquo cg)::P
	   aa := subResultantGcd
           ans:=subResultantGcd(f,g)$P
           gcd(cf,cg)*(ans exquo content ans)::P

        if % has CharacteristicNonZero then
	  import from List %
	  import from List List %
          charthRoot(ff: %): Partial % ==
	     import from Partial Vector %
             -- to take p'th root of f, solve the system X-fY=0,
             -- so solution is [x,y]
             -- with x^p=X and y^p=Y, then (x/y)^p = f
             zero? ff => [0]
             m:Matrix % := matrix [[1,-ff]]
             ans:= conditionP m
             ans case failed => [failed]
             (coerce(ans).1) exquo (coerce(ans).2)

        if % has Field then
          solveLinearPolynomialEquation(lf,g): Partial List P ==
            multiEuclidean(lf,g)$P
        else 
	  solveLinearPolynomialEquation(lf,g): Partial List P ==
               LPE ==> LinearPolynomialEquationByFractions %
	       import from LPE
               solveLinearPolynomialEquationByFractions(lf,g)

