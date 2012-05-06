-- FOR REFERENCE ONLY
SparseUnivariatePolynomial(R:Ring): UnivariatePolynomialCategory(R) with
     outputForm : (%,OutputForm) -> OutputForm
        ++ outputForm(p,var) converts the SparseUnivariatePolynomial p to
        ++ an output form (see \spadtype{OutputForm}) printed as a polynomial in the
        ++ output form variable.
     fmecg: (%,NonNegativeInteger,R,%) -> %
        ++ fmecg(p1,e,r,p2) finds X : p1 - r * X^e * p2
    == PolynomialRing(R,NonNegativeInteger)
  add
   --representations
   Term ==> Record(k:NonNegativeInteger,c:R)
   Rep  := List Term
   p:%
   n:NonNegativeInteger
   np: PositiveInteger
   FP ==> SparseUnivariatePolynomial %
   pp,qq: FP
   lpp:List FP

   -- for karatsuba
   kBound: NonNegativeInteger := 63
   upmp := UnivariatePolynomialMultiplicationPackage(R,%)

   makeSUP(p : %) : SparseUnivariatePolynomial(R) ==
       p pretend SparseUnivariatePolynomial(R)

   unmakeSUP(sp : SparseUnivariatePolynomial(R)) : % ==
       sp pretend %

   if R has FieldOfPrimeCharacteristic  then
         p ^ np == p ^ (np pretend NonNegativeInteger)
         p ^ n  ==
            null p => 0
            zero? n => 1
--            one? n => p
            (n = 1) => p
            empty? p.rest =>
              zero?(cc:=p.first.c ^ n) => 0
              [[n * p.first.k, cc]]
            -- not worth doing special trick if characteristic is too small
            if characteristic()$R < 3 then return expt(p,n pretend PositiveInteger)$RepeatedSquaring(%)
            y:%:=1
            -- break up exponent in qn * characteristic + rn
            -- exponentiating by the characteristic is fast
            rec := divide(n, characteristic()$R)
            qn:= rec.quotient
            rn:= rec.remainder
            repeat
                if rn = 1 then y := y * p
                if rn > 1 then y:= y * binomThmExpt([p.first], p.rest, rn)
                zero? qn => return y
                -- raise to the characteristic power
                p:= [[t.k * characteristic()$R , primeFrobenius(t.c)$R ]$Term for t in p]
                rec := divide(qn, characteristic()$R)
                qn:= rec.quotient
                rn:= rec.remainder
            y



   zero?(p): Boolean == empty?(p)
--   one?(p):Boolean == not empty? p and (empty? rest p and zero? first(p).k and one? first(p).c)
   one?(p):Boolean == not empty? p and (empty? rest p and zero? first(p).k and (first(p).c = 1))
   ground?(p): Boolean == empty? p or (empty? rest p and zero? first(p).k)
   multiplyExponents(p,n) == [ [u.k*n,u.c] for u in p]
   divideExponents(p,n) ==
     null p => p
     m:= (p.first.k :: Integer exquo n::Integer)
     m case "failed" => "failed"
     u:= divideExponents(p.rest,n)
     u case "failed" => "failed"
     [[m::Integer::NonNegativeInteger,p.first.c],:u]
   karatsubaDivide(p, n)  ==
     zero? n => [p, 0]
     lowp: Rep := p
     highp: Rep := []
     repeat
       if empty? lowp then break
       t := first lowp
       if t.k < n then break
       lowp := rest lowp
       highp := cons([subtractIfCan(t.k,n)::NonNegativeInteger,t.c]$Term,highp)
     [ reverse highp,  lowp]
   shiftRight(p, n)  ==
      [[subtractIfCan(t.k,n)::NonNegativeInteger,t.c]$Term for t in p]
   shiftLeft(p, n)  ==
      [[t.k + n,t.c]$Term for t in p]
   pomopo!(p1,r,e,p2) ==
          rout:%:= []
          for tm in p2 repeat
             e2:= e + tm.k
             c2:= r * tm.c
             c2 = 0 => "next term"
             while not null p1 and p1.first.k > e2 repeat
               (rout:=[p1.first,:rout]; p1:=p1.rest)  --use PUSH and POP?
             null p1 or p1.first.k < e2 => rout:=[[e2,c2],:rout]
             if (u:=p1.first.c + c2) ~= 0 then rout:=[[e2, u],:rout]
             p1:=p1.rest
          NRECONC(rout,p1)$Lisp

-- implementation using karatsuba algorithm conditionally
--
--   p1 * p2 ==
--     xx := p1::Rep
--     empty? xx => p1
--     yy := p2::Rep
--     empty? yy => p2
--     zero? first(xx).k => first(xx).c * p2
--     zero? first(yy).k => p1 * first(yy).c
--     (first(xx).k > kBound) and (first(yy).k > kBound) and (#xx > kBound) and (#yy > kBound) =>
--       karatsubaOnce(p1,p2)$upmp
--     xx := reverse xx
--     res : Rep := empty()
--     for tx in xx repeat res:= rep pomopo!( res,tx.c,tx.k,p2)
--     res


   univariate(p:%) == p pretend SparseUnivariatePolynomial(R)
   multivariate(sup:SparseUnivariatePolynomial(R),v:SingletonAsOrderedSet) ==
      sup pretend %
   univariate(p:%,v:SingletonAsOrderedSet) ==
     zero? p => 0
     monomial(leadingCoefficient(p)::%,degree p) +
         univariate(reductum p,v)
   multivariate(supp:SparseUnivariatePolynomial(%),v:SingletonAsOrderedSet) ==
     zero? supp => 0
     lc:=leadingCoefficient supp
     degree lc > 0 => error "bad form polynomial"
     monomial(leadingCoefficient lc,degree supp) +
         multivariate(reductum supp,v)
   if R has FiniteFieldCategory and R has PolynomialFactorizationExplicit then
     RXY ==> SparseUnivariatePolynomial SparseUnivariatePolynomial R
     squareFreePolynomial pp ==
        squareFree(pp)$UnivariatePolynomialSquareFree(%,FP)
     factorPolynomial pp ==
          (generalTwoFactor(pp pretend RXY)$TwoFactorize(R))
                      pretend Factored SparseUnivariatePolynomial %
     factorSquareFreePolynomial pp ==
          (generalTwoFactor(pp pretend RXY)$TwoFactorize(R))
                      pretend Factored SparseUnivariatePolynomial %
     gcdPolynomial(pp,qq) == gcd(pp,qq)$FP
     factor p == factor(p)$DistinctDegreeFactorize(R,%)
     solveLinearPolynomialEquation(lpp,pp) ==
       solveLinearPolynomialEquation(lpp, pp)$FiniteFieldSolveLinearPolynomialEquation(R,%,FP)
   else if R has PolynomialFactorizationExplicit then
     import PolynomialFactorizationByRecursionUnivariate(R,%)
     solveLinearPolynomialEquation(lpp,pp)==
       solveLinearPolynomialEquationByRecursion(lpp,pp)
     factorPolynomial(pp) ==
       factorByRecursion(pp)
     factorSquareFreePolynomial(pp) ==
       factorSquareFreeByRecursion(pp)

   if R has IntegralDomain then
    if R has Approximate then
     p1 exquo p2  ==
        null p2 => error "Division by 0"
        p2 = 1 => p1
        p1=p2 => 1
      --(p1.lastElt.c exquo p2.lastElt.c) case "failed" => "failed"
        rout:= []@List(Term)
        while not null p1 repeat
           (a:= p1.first.c exquo p2.first.c)
           a case "failed" => return "failed"
           ee:= subtractIfCan(p1.first.k, p2.first.k)
           ee case "failed" => return "failed"
           p1:= fmecg(p1.rest, ee, a, p2.rest)
           rout:= [[ee,a], :rout]
        null p1 => reverse(rout)::%    -- nreverse?
        "failed"
    else -- R not Approximate
     p1 exquo p2  ==
        null p2 => error "Division by 0"
        p2 = 1 => p1
      --(p1.lastElt.c exquo p2.lastElt.c) case "failed" => "failed"
        rout:= []@List(Term)
        while not null p1 repeat
           (a:= p1.first.c exquo p2.first.c)
           a case "failed" => return "failed"
           ee:= subtractIfCan(p1.first.k, p2.first.k)
           ee case "failed" => return "failed"
           p1:= fmecg(p1.rest, ee, a, p2.rest)
           rout:= [[ee,a], :rout]
        null p1 => reverse(rout)::%    -- nreverse?
        "failed"
   fmecg(p1,e,r,p2) ==       -- p1 - r * X^e * p2
          rout:%:= []
          r:= - r
          for tm in p2 repeat
             e2:= e + tm.k
             c2:= r * tm.c
             c2 = 0 => "next term"
             while not null p1 and p1.first.k > e2 repeat
               (rout:=[p1.first,:rout]; p1:=p1.rest)  --use PUSH and POP?
             null p1 or p1.first.k < e2 => rout:=[[e2,c2],:rout]
             if (u:=p1.first.c + c2) ~= 0 then rout:=[[e2, u],:rout]
             p1:=p1.rest
          NRECONC(rout,p1)$Lisp
   pseudoRemainder(p1,p2) ==
     null p2 => error "PseudoDivision by Zero"
     null p1 => 0
     co := p2.first.c
     e := p2.first.k
     p2 := p2.rest
     e1:=max((p1.first.k)::Integer-e+1,0)::NonNegativeInteger
     while not null p1 repeat
       if (u := subtractIfCan(p1.first.k, e)) case "failed" then break
       p1:=fmecg(co * p1.rest, u, p1.first.c, p2)
       e1:= (e1 - 1)::NonNegativeInteger
     e1 = 0 => p1
     co ^ e1 * p1
   toutput(t1:Term,v:OutputForm):OutputForm ==
     t1.k = 0 => t1.c :: OutputForm
     if t1.k = 1
       then mon:= v
       else mon := v ^ t1.k::OutputForm
     t1.c = 1 => mon
     t1.c = -1 and
          ((t1.c :: OutputForm) = (-1$Integer)::OutputForm)@Boolean => - mon
     t1.c::OutputForm * mon
   outputForm(p:%,v:OutputForm) ==
     l: List(OutputForm)
     l:=[toutput(t,v) for t in p]
     null l => (0$Integer)::OutputForm -- else FreeModule 0 problems
     reduce("+",l)

   coerce(p:%):OutputForm == outputForm(p, "?"::OutputForm)
   elt(p:%,val:R) ==
      null p => 0$R
      co:=p.first.c
      n:=p.first.k
      for tm in p.rest repeat
       co:= co * val ^ (n - (n:=tm.k))::NonNegativeInteger + tm.c
      n = 0 => co
      co * val ^ n
   elt(p:%,val:%) ==
      null p => 0$%
      coef:% := p.first.c :: %
      n:=p.first.k
      for tm in p.rest repeat
       coef:= coef * val ^ (n-(n:=tm.k))::NonNegativeInteger+(tm.c::%)
      n = 0 => coef
      coef * val ^ n

   monicDivide(p1:%,p2:%) ==
      null p2 => error "monicDivide: division by 0"
      leadingCoefficient p2 ~= 1 => error "Divisor Not Monic"
      p2 = 1 => [p1,0]
      null p1 => [0,0]
      degree p1 < (n:=degree p2) => [0,p1]
      rout:Rep := []
      p2 := p2.rest
      while not null p1 repeat
         (u := subtractIfCan(p1.first.k, n)) case "failed" => break
         rout:=[[u, p1.first.c], :rout]
         p1:=fmecg(p1.rest, rout.first.k, rout.first.c, p2)
      [reverse!(rout),p1]

   if R has IntegralDomain then
       discriminant(p) == discriminant(p)$PseudoRemainderSequence(R,%)
--     discriminant(p) ==
--       null p or zero?(p.first.k) => error "cannot take discriminant of constants"
--       dp:=differentiate p
--       corr:=  p.first.c ^ ((degree p - 1 - degree dp)::NonNegativeInteger)
--       (-1)^((p.first.k*(p.first.k-1)) quo 2):NonNegativeInteger
--         * (corr * resultant(p,dp) exquo p.first.c)::R

       subResultantGcd(p1,p2) == subResultantGcd(p1,p2)$PseudoRemainderSequence(R,%)
--     subResultantGcd(p1,p2) ==    --args # 0, non-coef, prim, ans not prim
--       --see algorithm 1 (p. 4) of Brown's latest (unpublished) paper
--       if p1.first.k < p2.first.k then (p1,p2):=(p2,p1)
--       p:=pseudoRemainder(p1,p2)
--       co:=1$R;
--       e:= (p1.first.k - p2.first.k):NonNegativeInteger
--       while not null p and p.first.k ~= 0 repeat
--         p1:=p2; p2:=p; p:=pseudoRemainder(p1,p2)
--         null p or p.first.k = 0 => "enuf"
--         co:=(p1.first.c ^ e exquo co ^ max(0, (e-1))::NonNegativeInteger)::R
--         e:= (p1.first.k - p2.first.k):NonNegativeInteger;  c1:=co^e
--         p:=[[tm.k,((tm.c exquo p1.first.c)::R exquo c1)::R] for tm in p]
--       if null p then p2 else 1$%

       resultant(p1,p2) == resultant(p1,p2)$PseudoRemainderSequence(R,%)
--     resultant(p1,p2) ==      --SubResultant PRS Algorithm
--        null p1 or null p2 => 0$R
--        0 = degree(p1) => ((first p1).c)^degree(p2)
--        0 = degree(p2) => ((first p2).c)^degree(p1)
--        if p1.first.k < p2.first.k then
--          (if odd?(p1.first.k) then p1:=-p1;  (p1,p2):=(p2,p1))
--        p:=pseudoRemainder(p1,p2)
--        co:=1$R;  e:=(p1.first.k-p2.first.k):NonNegativeInteger
--        while not null p repeat
--           if not odd?(e) then p:=-p
--           p1:=p2;  p2:=p;  p:=pseudoRemainder(p1,p2)
--           co:=(p1.first.c ^ e exquo co ^ max(e:Integer-1,0):NonNegativeInteger)::R
--           e:= (p1.first.k - p2.first.k):NonNegativeInteger;  c1:=co^e
--           p:=(p exquo ((leadingCoefficient p1) * c1))::%
--        degree p2 > 0 => 0$R
--        (p2.first.c^e exquo co^((e-1)::NonNegativeInteger))::R
   if R has GcdDomain then
     content(p) == if null p then 0$R else "gcd"/[tm.c for tm in p]
        --make CONTENT more efficient?

     primitivePart(p) ==
        null p => p
        ct :=content(p)
        unitCanonical((p exquo ct)::%)
               -- exquo  present since % is now an IntegralDomain

     gcd(p1,p2) ==
          gcdPolynomial(p1 pretend SparseUnivariatePolynomial R,
                        p2 pretend SparseUnivariatePolynomial R) pretend %

   if R has Field then
     divide( p1, p2)  ==
       zero? p2 => error "Division by 0"
--       one? p2 => [p1,0]
       (p2 = 1) => [p1,0]
       ct:=inv(p2.first.c)
       n:=p2.first.k
       p2:=p2.rest
       rout:=empty()$List(Term)
       while p1 ~= 0 repeat
          (u := subtractIfCan(p1.first.k, n)) case "failed" => break
          rout:=[[u, ct * p1.first.c], :rout]
          p1:=fmecg(p1.rest, rout.first.k, rout.first.c, p2)
       [reverse!(rout),p1]

     p / co == inv(co) * p
