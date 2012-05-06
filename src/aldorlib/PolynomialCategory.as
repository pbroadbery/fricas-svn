--DEPS: OrderedAbelianMonoidSup PartialDifferentialRing FiniteAbelianMonoidRing InnerEvalable 
--DEPS: FullyLinearlyExplicitRingOver PolynomialCategory0 GcdDomain0 SparseUnivariatePolynomial_R
--DEPS: List_ExtensibleLinearAggregate Matrix_MatrixCategory
#include "axiom.as"
#pile

import from Boolean
-- SKIPPED: Pattern, Factored
-- USES GcdDomain0 in place of GcdDomain
PolynomialCategory(R:Ring, E:OrderedAbelianMonoidSup, VarSet:OrderedSet):
        Category ==
  PolynomialCategory0(R, E, VarSet) with
    -- operations
   if R has Comparable then Comparable
   -- OrderedRing view removed to allow EXPR to define abs
   --if R has OrderedRing then OrderedRing
   if (R has ConvertibleTo InputForm) and
      (VarSet has ConvertibleTo InputForm) then
        ConvertibleTo InputForm
--   if (R has ConvertibleTo Pattern Integer) and
--      (VarSet has ConvertibleTo Pattern Integer) then
--        ConvertibleTo Pattern Integer
--   if (R has ConvertibleTo Pattern Float) and
--      (VarSet has ConvertibleTo Pattern Float) then
--        ConvertibleTo Pattern Float
--   if (R has PatternMatchable Integer) and
--      (VarSet has PatternMatchable Integer) then
--        PatternMatchable Integer
--   if (R has PatternMatchable Float) and
--      (VarSet has PatternMatchable Float) then
--        PatternMatchable Float
   if R has CommutativeRing then
     resultant : (%,%,VarSet) -> %
        ++ resultant(p,q,v) returns the resultant of the polynomials
        ++ p and q with respect to the variable v.
     discriminant : (%,VarSet) -> %
        ++ discriminant(p,v) returns the disriminant of the polynomial p
        ++ with respect to the variable v.
   if R has GcdDomain0 then
     GcdDomain0
     content: (%,VarSet) -> %
       ++ content(p,v) is the gcd of the coefficients of the polynomial p
       ++ when p is viewed as a univariate polynomial with respect to the
       ++ variable v.
       ++ Thus, for polynomial 7*x^2*y + 14*x*y^2, the gcd of the
       ++ coefficients with respect to x is 7*y.
     primitivePart: % -> %
       ++ primitivePart(p) returns the unitCanonical associate of the
       ++ polynomial p with its content divided out.
     primitivePart: (%,VarSet) -> %
       ++ primitivePart(p,v) returns the unitCanonical associate of the
       ++ polynomial p with its content with respect to the variable v
       ++ divided out.
--     squareFree: % -> Factored %
       ++ squareFree(p) returns the square free factorization of the
       ++ polynomial p.
--     squareFreePart: % -> %
       ++ squareFreePart(p) returns product of all the irreducible factors
       ++ of polynomial p each taken with multiplicity one.

   -- assertions
   if R has canonicalUnitNormal then canonicalUnitNormal
            -- we can choose a unique representative for each
            -- associate class.
            -- This normalization is chosen to be normalization of
            -- leading coefficient (by default).
--   if R has PolynomialFactorizationExplicit then
--      PolynomialFactorizationExplicit
   default
    default p, p1, p2:%
    default v, var:VarSet
    default ln:List NonNegativeInteger
    default lv, vars:List VarSet
    default n:NonNegativeInteger
    default pp,qq:SparseUnivariatePolynomial %
    default mvar: VarSet
    default ch: Integer
    import from UniversalSegment Integer
    import from List List %
    import from List %
    import from List List R
    import from List R
    import from R
    import from List E
    import from E
    import from Partial %
    import from Partial R

    if R has CommutativeRing then
        resultant(p1,p2,mvar): % ==
	  u1 := univariate(p1, mvar)
	  u2 := univariate(p2, mvar)
          resultant(u1, u2)

        discriminant(p,var): % ==
          u1 := univariate(p,var)
          discriminant(u1)

    if R has IntegralDomain then FullyLinearlyExplicitRingOver R
    if R has IntegralDomain then
      allMonoms(l:List %):List(%) ==
        removeDuplicates! concat [primitiveMonomials p for p in l]
      P2R(p:%, b:List E, n:NonNegativeInteger):Vector(R) ==
        w := new(n, 0)$Vector(R)
        for i in minIndex w .. maxIndex w for bj in b repeat
          qsetelt!(w, i, coefficient(p, bj))
        w
      eq2R(l:List %, b:List E):Matrix(R) ==
        matrix [[coefficient(p, bj) for p in l] for bj in b]
      reducedSystem(m:Matrix %):Matrix(R) ==
        l := listOfLists m
        b := removeDuplicates! concat([allMonoms r for r in l]$List(List(%)))
        d := [degree bj for bj in b]
        mm := eq2R(first l, d)
        l := rest l
        while not empty? l repeat
          mm := vertConcat(mm, eq2R(first l, d))
          l := rest l
        mm
      reducedSystem(mat1:Matrix %, vv:Vector %): Record(mat:Matrix R, vec:Vector R) ==
        import from Matrix R
        l := listOfLists mat1
        r := entries vv
        b : List % := removeDuplicates! concat(allMonoms r,
                          concat([allMonoms s for s in l]$List(List(%))))
        d := [degree bj for bj in b]
        n := #d
        mm := eq2R(first l, d)
        w := P2R(first r, d, n)
        l := rest l
        r := rest r
        while not empty? l repeat
          mm := vertConcat(mm, eq2R(first l, d))
          w := concat(w, P2R(first r, d, n))
          l := rest l
          r := rest r
        [mm, w]

--    if R has PolynomialFactorizationExplicit then
--       -- we might be in trouble if its actually only
--       -- a univariate polynomial category - have to remember to
--       -- over-ride these in UnivariatePolynomialCategory
--       PFBR ==>PolynomialFactorizationByRecursion(R,E,VarSet,%)
--       gcdPolynomial(pp,qq) ==
--          gcdPolynomial(pp,qq)$GeneralPolynomialGcdPackage(E,VarSet,R,%)
--       solveLinearPolynomialEquation(lpp,pp) ==
--         solveLinearPolynomialEquationByRecursion(lpp,pp)$PFBR
--       factorPolynomial(pp) ==
--         factorByRecursion(pp)$PFBR
--       factorSquareFreePolynomial(pp) ==
--         factorSquareFreeByRecursion(pp)$PFBR
--       factor p ==
--         v:Union(VarSet,"failed"):=mainVariable p
--         v case "failed" =>
--           ansR:=factor leadingCoefficient p
--           makeFR(unit(ansR)::%,
--                  [[w.flg,w.fctr::%,w.xpnt] for w in factorList ansR])
--         up:SparseUnivariatePolynomial %:=univariate(p,v)
--         ansSUP:=factorByRecursion(up)$PFBR
--         makeFR(multivariate(unit(ansSUP),v),
--                [[ww.flg,multivariate(ww.fctr,v),ww.xpnt]
--                 for ww in factorList ansSUP])
--      if R has CharacteristicNonZero then
--          conditionP: Matrix % -> Partial Vector %
--          default mat: Matrix %
--
--          conditionP mat: Partial Vector % ==
--            import from Fold List %
--	    import from Matrix R
--	    import from Integer
--            ll:=listOfLists transpose mat   -- hence each list corresponds to a
--                                            -- column, i.e. to one variable
--            llR:List List R := [ empty() for z in first ll]
--            monslist:List List % := empty()
--            ch : Integer := characteristic()$%::Integer
--            for l in ll repeat
--                mons:= setUnion/[primitiveMonomials u for u in l]
--                redmons:List % :=[]
--                for m in mons repeat
--                    vars:=variables m
--                    degs := degree(m,vars)
--                    local deg1:List NonNegativeInteger
----                    deg1:=[ failed?((nd:=(d::Integer) exquo ch)
----                               => return failed() ;
----                                nd::Integer::NonNegativeInteger)
----                           for d in degs ]
--	            deg1: List NonNegativeInteger := never -- NEED TO FIX ABOVE 4 LINES!
--                    redmons:=cons(monomial(1,vars,deg1), redmons)
--                    llR: List List R :=[cons(ground coefficient(u,vars,degs),v) for u in l for v in llR]
--                monslist:=cons(redmons, monslist)
--            ans := conditionP transpose matrix llR
--            failed? ans => failed()
--            i:NonNegativeInteger:=0
--            success([ (+)/[m*(ans.(i:=i+1))::% for m in rmons ]
--                    for rmons in monslist])
--
    if R has CharacteristicNonZero then

          charthRoot p: Partial % ==
            vars:= variables p
            empty? vars =>
              ans := charthRoot ground p
              failed? ans => failed()
              success(ans::R::%)
            ch:=characteristic()$%::Integer
            charthRootlv(p,vars,ch)

          local charthRootlv(p,vars,ch): Partial % ==
            import from Partial Integer
            empty? vars =>
              ans1 := charthRoot ground p
              failed? ans1 => failed()
              success(ans1::R::%)
            v:=first vars
            vars:=rest vars
            d:=degree(p,v)
            ans: % := 0
            while (d>0) repeat
               failed?(dd:=(d::Integer exquo ch::Integer)) =>
                      return failed()
               cp:=coefficient(p,v,d)
               p:=p-monomial(cp,v,d)
               ansx:=charthRootlv(cp,vars,ch)
               failed? ansx => return failed()
               d:=degree(p,v)
               ans:=ans+monomial(ansx::%,v,dd::Integer::NonNegativeInteger)
            ansx := charthRootlv(p,vars,ch)
            failed? ansx => return failed()
            return success(ans + ansx::%)

    if R has GcdDomain0 then
--      if R has EuclideanDomain and R has CharacteristicZero then
--       squareFree p == squareFree(p)$MultivariateSquareFree(E,VarSet,R,%)
--      else
--        squareFree p == squareFree(p)$PolynomialSquareFree(VarSet,E,R,%)
--      squareFreePart p ==
--        unit(s := squareFree p) * (*)/[f.factor for f in factors s]
      content(p,v): % == content univariate(p,v)

      import from Record(unit:%,canonical:%,associate:%)
      primitivePart p: % ==
        zero? p => p
        unitNormal((p exquo content p) ::%).canonical

      primitivePart(p,v): % ==
        zero? p => p
        unitNormal((p exquo content(p,v)) ::%).canonical

    if R has Comparable then
      smaller?(p:%, q:%): Boolean ==
        (dp:= degree p) < (dq := degree q) =>
             smaller?(0, leadingCoefficient q)
        dq < dp => smaller?(leadingCoefficient p, 0)
        smaller?(leadingCoefficient(p - q), 0)

--      if (R has PatternMatchable Integer) and
--         (VarSet has PatternMatchable Integer) then
--           patternMatch(p:%, pat:Pattern Integer,
--            l:PatternMatchResult(Integer, %)) ==
--              patternMatch(p, pat,
--                l)$PatternMatchPolynomialCategory(Integer,E,VarSet,R,%)
--      if (R has PatternMatchable Float) and
--         (VarSet has PatternMatchable Float) then
--           patternMatch(p:%, pat:Pattern Float,
--            l:PatternMatchResult(Float, %)) ==
--              patternMatch(p, pat,
--                l)$PatternMatchPolynomialCategory(Float,E,VarSet,R,%)
--
--    if (R has ConvertibleTo Pattern Integer) and
--       (VarSet has ConvertibleTo Pattern Integer) then
--         convert(x:%):Pattern(Integer) ==
--           map(convert, convert,
--              x)$PolynomialCategoryLifting(E,VarSet,R,%,Pattern Integer)
--    if (R has ConvertibleTo Pattern Float) and
--       (VarSet has ConvertibleTo Pattern Float) then
--         convert(x:%):Pattern(Float) ==
--           map(convert, convert,
--            x)$PolynomialCategoryLifting(E, VarSet, R, %, Pattern Float)

    if (R has ConvertibleTo InputForm) and
       (VarSet has ConvertibleTo InputForm) then
         convert(p:%):InputForm == never
  --         map(convert, convert, p)$PolynomialCategoryLifting(E,VarSet,R,%,InputForm)
