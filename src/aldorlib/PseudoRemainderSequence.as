--DEPS: UnivariatePolynomialCategory0 GcdDomain0 Finite Vector
#include "axiom.as"
#pile
import from Boolean
import from System
import from String

NNI ==> NonNegativeInteger
LC  ==> leadingCoefficient

PseudoRemainderSequence(R: IntegralDomain, polR: UnivariatePolynomialCategory0 R) : 
 with
       resultant : (polR, polR) -> R
         ++ \axiom{resultant(P, Q)} returns the resultant
         ++ of \axiom{P} and \axiom{Q}

       resultantEuclidean : (polR, polR) ->
                          Record(coef1 : polR, coef2 : polR, resultant : R)
         ++ \axiom{resultantEuclidean(P,Q)} carries out the equality
         ++ \axiom{coef1*P + coef2*Q = resultant(P,Q)}

       semiResultantEuclidean2 : (polR, polR) ->
                          Record(coef2 : polR, resultant : R)
         ++ \axiom{semiResultantEuclidean2(P,Q)} carries out the equality
         ++ \axiom{...P + coef2*Q = resultant(P,Q)}.
         ++ Warning: \axiom{degree(P) >= degree(Q)}.

       semiResultantEuclidean1 : (polR, polR) ->
                          Record(coef1 : polR, resultant : R)
         ++ \axiom{semiResultantEuclidean1(P,Q)} carries out the equality
         ++ \axiom{coef1.P + ? Q = resultant(P,Q)}.

       indiceSubResultant : (polR, polR, NNI) -> polR
         ++ \axiom{indiceSubResultant(P, Q, i)} returns
         ++ the subresultant of indice \axiom{i}

       indiceSubResultantEuclidean : (polR, polR, NNI) ->
                       Record(coef1 : polR, coef2 : polR, subResultant : polR)
         ++ \axiom{indiceSubResultant(P, Q, i)} returns
         ++ the subresultant \axiom{S_i(P,Q)} and carries out the equality
         ++ \axiom{coef1*P + coef2*Q = S_i(P,Q)}

       semiIndiceSubResultantEuclidean : (polR, polR, NNI) ->
                          Record(coef2 : polR, subResultant : polR)
         ++ \axiom{semiIndiceSubResultantEuclidean(P, Q, i)} returns
         ++ the subresultant \axiom{S_i(P,Q)} and carries out the equality
         ++ \axiom{...P + coef2*Q = S_i(P,Q)}
         ++ Warning: \axiom{degree(P) >= degree(Q)}.

       degreeSubResultant : (polR, polR, NNI) -> polR
         ++ \axiom{degreeSubResultant(P, Q, d)} computes
         ++ a subresultant of degree \axiom{d}.

       degreeSubResultantEuclidean : (polR, polR, NNI) ->
                       Record(coef1 : polR, coef2 : polR, subResultant : polR)
         ++ \axiom{indiceSubResultant(P, Q, i)} returns
         ++ a subresultant \axiom{S} of degree \axiom{d}
         ++ and carries out the equality \axiom{coef1*P + coef2*Q = S_i}.

       semiDegreeSubResultantEuclidean : (polR, polR, NNI) ->
                          Record(coef2 : polR, subResultant : polR)
         ++ \axiom{indiceSubResultant(P, Q, i)} returns
         ++ a subresultant \axiom{S} of degree \axiom{d}
         ++ and carries out the equality \axiom{...P + coef2*Q = S_i}.
         ++ Warning: \axiom{degree(P) >= degree(Q)}.

       lastSubResultant : (polR, polR) -> polR
         ++ \axiom{lastSubResultant(P, Q)} computes
         ++ the last non zero subresultant of \axiom{P} and \axiom{Q}

       lastSubResultantEuclidean : (polR, polR) ->
                       Record(coef1 : polR, coef2 : polR, subResultant : polR)
         ++ \axiom{lastSubResultantEuclidean(P, Q)} computes
         ++ the last non zero subresultant \axiom{S}
         ++ and carries out the equality \axiom{coef1*P + coef2*Q = S}.

       semiLastSubResultantEuclidean : (polR, polR) ->
                       Record(coef2 : polR, subResultant : polR)
         ++ \axiom{semiLastSubResultantEuclidean(P, Q)} computes
         ++ the last non zero subresultant \axiom{S}
         ++ and carries out the equality \axiom{...P + coef2*Q = S}.
         ++ Warning: \axiom{degree(P) >= degree(Q)}.

       subResultantGcd : (polR, polR) -> polR
         ++ \axiom{subResultantGcd(P, Q)} returns the gcd
         ++ of two primitive polynomials \axiom{P} and \axiom{Q}.

       subResultantGcdEuclidean : (polR, polR)
                     -> Record(coef1 : polR, coef2 : polR, gcd : polR)
         ++ \axiom{subResultantGcdEuclidean(P,Q)} carries out the equality
         ++ \axiom{coef1*P + coef2*Q = +/- S_i(P,Q)}
         ++ where the degree (not the indice)
         ++ of the subresultant \axiom{S_i(P,Q)} is the smaller as possible.

       semiSubResultantGcdEuclidean2 : (polR, polR)
                                   -> Record(coef2 : polR, gcd : polR)
         ++ \axiom{semiSubResultantGcdEuclidean2(P,Q)} carries out the equality
         ++ \axiom{...P + coef2*Q = +/- S_i(P,Q)}
         ++ where the degree (not the indice)
         ++ of the subresultant \axiom{S_i(P,Q)} is the smaller as possible.
         ++ Warning: \axiom{degree(P) >= degree(Q)}.

       semiSubResultantGcdEuclidean1: (polR, polR)->Record(coef1: polR, gcd: polR)
         ++ \axiom{semiSubResultantGcdEuclidean1(P,Q)} carries out the equality
         ++ \axiom{coef1*P + ? Q = +/- S_i(P,Q)}
         ++ where the degree (not the indice)
         ++ of the subresultant \axiom{S_i(P,Q)} is the smaller as possible.

       discriminant : polR -> R
         ++ \axiom{discriminant(P, Q)} returns the discriminant
         ++ of \axiom{P} and \axiom{Q}.

       discriminantEuclidean : polR ->
                           Record(coef1 : polR, coef2 : polR, discriminant : R)
         ++ \axiom{discriminantEuclidean(P)} carries out the equality
         ++ \axiom{coef1 * P + coef2 * D(P) = discriminant(P)}.

       semiDiscriminantEuclidean : polR ->
                           Record(coef2 : polR, discriminant : R)
         ++ \axiom{discriminantEuclidean(P)} carries out the equality
         ++ \axiom{...P + coef2 * D(P) = discriminant(P)}.
         ++ Warning: \axiom{degree(P) >= degree(Q)}.

       chainSubResultants : (polR, polR) -> List(polR)
         ++ \axiom{chainSubResultants(P, Q)} computes the list
         ++ of non zero subresultants of \axiom{P} and \axiom{Q}.

       schema : (polR, polR) -> List(NNI)
         ++ \axiom{schema(P,Q)} returns the list of degrees of
         ++ non zero subresultants of \axiom{P} and \axiom{Q}.

       if R has GcdDomain0 then
         resultantReduit : (polR, polR) -> R
           ++ \axiom{resultantReduit(P,Q)} returns the "reduce resultant"
           ++ of \axiom{P} and \axiom{Q}.

         resultantReduitEuclidean : (polR, polR) ->
                        Record(coef1 : polR, coef2 : polR, resultantReduit : R)
            ++ \axiom{resultantReduitEuclidean(P,Q)} returns
            ++ the "reduce resultant" and carries out the equality
            ++ \axiom{coef1*P + coef2*Q = resultantReduit(P,Q)}.

         semiResultantReduitEuclidean : (polR, polR) ->
                        Record(coef2 : polR, resultantReduit : R)
           ++ \axiom{semiResultantReduitEuclidean(P,Q)} returns
           ++ the "reduce resultant" and carries out the equality
           ++ \axiom{...P + coef2*Q = resultantReduit(P,Q)}.

         gcd : (polR, polR) -> polR
           ++ \axiom{gcd(P, Q)} returns the gcd of \axiom{P} and \axiom{Q}.

       -- sub-routines exported for convenience ----------------------------

       * : (R, Vector(polR)) -> Vector(polR)
           ++ \axiom{r * v} computes the product of \axiom{r} and \axiom{v}

       exquo : (Vector(polR), R) -> Vector(polR)
         ++ \axiom{v exquo r} computes
         ++ the exact quotient of \axiom{v} by \axiom{r}

       pseudoDivide : (polR, polR) ->
                                Record(coef:R, quotient:polR, remainder:polR)
         ++ \axiom{pseudoDivide(P,Q)} computes the pseudoDivide
         ++ of \axiom{P} by \axiom{Q}.

       divide : (polR, polR) -> Record(quotient : polR, remainder : polR)
         ++ \axiom{divide(F,G)} computes quotient and rest
         ++ of the exact euclidean division of \axiom{F} by \axiom{G}.

       Lazard : (R, R, NNI) -> R
         ++ \axiom{Lazard(x, y, n)} computes \axiom{x^n/y^(n-1)}

       Lazard2 : (polR, R, R, NNI) -> polR
         ++ \axiom{Lazard2(F, x, y, n)} computes  \axiom{(x/y)^(n-1) * F}

       next__sousResultant2 : (polR, polR, polR, R) -> polR
         ++ \axiom{nextsousResultant2(P, Q, Z, s)} returns
         ++ the subresultant \axiom{S_{e-1}} where
         ++ \axiom{P ~ S_d,  Q = S_{d-1},  Z = S_e,  s = lc(S_d)}

       resultant__naif : (polR, polR) -> R
         ++ \axiom{resultantEuclidean_naif(P,Q)} returns
         ++ the resultant of \axiom{P} and \axiom{Q} computed
         ++ by means of the naive algorithm.

       resultantEuclidean__naif : (polR, polR) ->
                          Record(coef1 : polR, coef2 : polR, resultant : R)
         ++ \axiom{resultantEuclidean_naif(P,Q)} returns
         ++ the extended resultant of \axiom{P} and \axiom{Q} computed
         ++ by means of the naive algorithm.

       semiResultantEuclidean__naif : (polR, polR) ->
                          Record(coef2 : polR, resultant : R)
         ++ \axiom{resultantEuclidean_naif(P,Q)} returns
         ++ the semi-extended resultant of \axiom{P} and \axiom{Q} computed
         ++ by means of the naive algorithm.

==  add
    import from Record(coef2 : polR, resultant : R) 
    import from Record(coef1 : polR, coef2 : polR, resultant : R)
    import from Record(coef:R, quotient:polR, remainder:polR)
    import from Record(coef1 : polR, coef2 : polR, subResultant : polR)
    import from Record(quotient : polR, remainder : polR)
    import from Record(coef1 : polR, coef2 : polR, subResultant : polR)

    import from UniversalSegment Integer
    import from Integer
    import from NonNegativeInteger
    import from Partial polR
    import from Partial R
    import from polR
    import from R

    local construct(coef:R, quotient:polR, remainder:polR): Record(coef:R, quotient:polR, remainder:polR) == 
    	  [coef, quotient, remainder]
    local construct(coef1: polR, coef2:polR, resultant: R): Record(coef1:polR, coef2:polR, resultant: R) == 
    	  [coef1, coef2, resultant]
    local construct(quotient:polR, remainder:polR): Record(quotient:polR, remainder:polR) == 
    	  [quotient, remainder]
	  
    local construct(coef2 : polR, resultant : R): Record(coef2 : polR, resultant : R) == [coef2, resultant]

    local construct(coef1: polR, coef2: polR, subResultant: polR): Record(coef1: polR, coef2: polR, subResultant: polR) == [coef1, coef2, subResultant]

    X : polR := monomial(1$R,1)
    
    (r : R) * (v : Vector(polR)): Vector polR == r::polR * v
              -- the instruction  map(r * #1, v) is slower !?

    (v : Vector(polR)) exquo (r : R): Vector polR == 
          map((p1: polR): polR +-> (p1 exquo r)::polR, v)

    pseudoDivide(P : polR, Q : polR) :
                                 Record(coef:R,quotient:polR,remainder:polR) ==
    -- computes the pseudoDivide of P by Q
       import from Integer
       zero?(Q) => error("PseudoDivide$PRS : division by 0")
       zero?(P) => record(1, 0, P)
       lcQ : R := LC(Q)
       (degP, degQ) := (degree(P), degree(Q))
       degP < degQ => record(1, 0, P)
       Q := reductum(Q)
       i : NNI := (degP - degQ + 1)::NNI
       co : R := lcQ^i
       quot : polR := 0$polR
       while (delta : Integer := degree(P) - degQ) >= 0 repeat
         i := (i - 1)::NNI
         mon := monomial(LC(P), delta::NNI)$polR
         quot := quot + lcQ^i * mon
         P := lcQ * reductum(P) - mon * Q
       P := lcQ^i * P
       return record(co, quot, P)

    divide(F : polR, G : polR) : Record(quotient : polR, remainder : polR)==
    -- computes quotient and rest of the exact euclidean division of F by G
         import from Integer
         lcG : R := LC(G)
         degG : NNI := degree(G)
         zero?(degG) => ( F := (F exquo lcG)::polR; return record(F, 0))
         G : polR := reductum(G)
         quot : polR := 0
         while (delta := degree(F) - degG) >= 0 repeat
            mon : polR := monomial((LC(F) exquo lcG)::R, delta::NNI)
            quot := quot + mon
            F := reductum(F) - mon * G
         return record(quot, F)

    resultant__naif(P : polR, Q : polR) : R ==
       import from Record(quotient : polR, remainder : polR)
    -- valid over a field
       a : R := 1
       repeat
          zero?(Q) => return 0
          (degP, degQ) := (degree(P), degree(Q))
          if odd?(degP) and odd?(degQ) then a := - a
          zero?(degQ) => return (a * LC(Q)^degP)
          U : polR := divide(P, Q).remainder
          a := a * LC(Q)^(degP - degree(U))::NNI
          (P, Q) := (Q, U)

    resultantEuclidean__naif(P : polR, Q : polR) :
                       Record(coef1 : polR, coef2 : polR, resultant : R) ==
    -- valid over a field.
       import from Record(quotient : polR, remainder : polR)
       a : R := 1
       old__cf1 : polR := 1 ; cf1 : polR := 0
       old__cf2 : polR := 0 ; cf2 : polR := 1
       repeat
          zero?(Q) => return record(0, 0, 0@R)
          (degP, degQ) := (degree(P), degree(Q))
          if odd?(degP) and odd?(degQ) then a := -a
          if zero?(degQ) then
             a := a * LC(Q)^(degP-1)::NNI
             return record(a*cf1, a*cf2, a*LC(Q))
          divid := divide(P,Q)
          a := a * LC(Q)^(degP - degree(divid.remainder))::NNI
          (P, Q) := (Q, divid.remainder)
          (old__cf1, old__cf2, cf1, cf2) := (cf1, cf2,
                old__cf1 - divid.quotient * cf1, old__cf2 - divid.quotient * cf2)

    semiResultantEuclidean__naif(P : polR, Q : polR) :
                       Record(coef2 : polR, resultant : R) ==
    -- valid over a field
       import from Record(quotient : polR, remainder : polR)
       a : R := 1
       old__cf2 : polR := 0 ; cf2 : polR := 1
       repeat
          zero?(Q) => return record(0, 0)
          (degP, degQ) := (degree(P), degree(Q))
          if odd?(degP) and odd?(degQ) then a := -a
          if zero?(degQ) then
             a := a * LC(Q)^(degP-1)::NNI
             return record(a*cf2, a*LC(Q))
          divid := divide(P,Q)
          a := a * LC(Q)^(degP - degree(divid.remainder))::NNI
          (P, Q) := (Q, divid.remainder)
          (old__cf2, cf2) := (cf2, old__cf2 - divid.quotient * cf2)

    Lazard(x : R, y : R, n : NNI) : R ==
       import from Integer
       zero?(n) => error("Lazard$PRS : n = 0")
--       one?(n) => x
       (n = 1) => x
       a : NNI := 1
       while n >= (b := 2::NNI*a) repeat a := b
       c : R := x
       n := (n - a)::NNI
       repeat                    --  c = x^i / y^(i-1),  i=n__0 quo a,  a=2^?
--          one?(a) => return c
          (a = 1) => return c
          a := a quo (2::NNI)
          c := ((c * c) exquo y)::R
          if n >= a then ( c := ((c * x) exquo y)::R ; n := (n - a)::NNI )

    Lazard2(F : polR, x : R, y : R, n : NNI) : polR ==
       zero?(n) => error("Lazard2$PRS : n = 0")
--       one?(n) => F
       (n = 1) => F
       x := Lazard(x, y, (n-1)::NNI)
       return ((x * F) exquo y)::polR

    Lazard3(V : Vector(polR), x : R, y : R, n : NNI) : Vector(polR) ==
    -- computes x^(n-1) * V / y^(n-1)
       zero?(n) => error("Lazard2$prs : n = 0")
--       one?(n) => V
       (n = 1) => V
       x := Lazard(x, y, (n-1)::NNI)
       return ((x * V) exquo y)

    next__sousResultant2(P : polR, Q : polR, Z : polR, s : R) : polR ==
       import from UniversalSegment Integer
       import from Integer
       (lcP, c, se) := (LC(P), LC(Q), LC(Z))
       (d, e) := (degree(P), degree(Q))
       (P, Q, H) := (reductum(P), reductum(Q), - reductum(Z))
       A : polR := coefficient(P, e) * H
       for i in e::Integer+1..d-1 repeat
          H := if degree(H)::Integer = e-1 then
                  X * reductum(H) - ((LC(H) * Q) exquo c)::polR
               else
                  X * H
          -- H = s__e * X^i mod S__d-1
          A := coefficient(P, i::NNI) * H + A
       while degree(P) >= e repeat P := reductum(P)
       A := A + se * P            --  A = s__e * reductum(P__0)       mod S__d-1
       A := (A exquo lcP)::polR   --  A = s__e * reductum(S__d) / s__d mod S__d-1
       A := if degree(H)::Integer = e-1 then
               c * (X * reductum(H) + A) - LC(H) * Q
            else
               c * (X * H + A)
       A := (A exquo s)::polR                    -- A = +/- S__e-1
       return (if odd?(d-e) then A else - A)

    next__sousResultant3(VP : Vector(polR), VQ : Vector(polR), s : R, ss : R) :
                                                      Vector(polR) ==
    -- P ~ S__d,  Q = S__d-1,  s = lc(S__d),  ss = lc(S__e)
       import from Integer
       (P, Q) := (VP.1, VQ.1)
       (lcP, c) := (LC(P), LC(Q))
       e : NNI := degree(Q)
--       if one?(delta := degree(P) - e) then                   -- algo__new
       if ((delta := degree(P) - e) = 1) then                   -- algo__new
         VP := c * VP - coefficient(P, e) * VQ
         VP := VP exquo lcP
         VP := c * (VP - X * VQ) + coefficient(Q, (e-1)::NNI) * VQ
         VP := VP exquo s
       else                                    -- algorithm of Lickteig - Roy
         (r, rr) := (s * lcP, ss * c)
         divid := divide(rr * P, Q)
         VP.1 := (divid.remainder exquo r)::polR
         for i in 2..#VP::Integer repeat
           VP.i := rr * VP.i - VQ.i * divid.quotient
           VP.i := (VP.i exquo r)::polR
       return (if odd?(delta) then VP else - VP)

    algo__new(P : polR, Q : polR) : R ==
       delta : NNI := (degree(P) - degree(Q))::NNI
       s : R := LC(Q)^delta
       (P, Q) := (Q, pseudoRemainder(P, -Q))
       repeat
          -- P = S__c-1 (except the first turn : P ~ S__c-1),
          -- Q = S__d-1,  s = lc(S__d)
          zero?(Q) => return 0
          delta := (degree(P) - degree(Q))::NNI
          Z : polR := Lazard2(Q, LC(Q), s, delta)
          -- Z = S__e ~ S__d-1
          zero?(degree(Z)) => return LC(Z)
          (P, Q) := (Q, next__sousResultant2(P, Q, Z, s))
          s := LC(Z)

    resultant(P : polR, Q : polR) : R ==
       zero?(Q) or zero?(P) => 0
       if degree(P) < degree(Q) then
          (P, Q) := (Q, P)
          if odd?(degree(P)) and odd?(degree(Q)) then Q := - Q
       zero?(degree(Q)) => LC(Q)^degree(P)
       -- degree(P) >= degree(Q) > 0
       R has Finite => resultant__naif(P, Q)
       return algo__new(P, Q)

    subResultantEuclidean(P : polR, Q : polR) :
                          Record(coef1 : polR, coef2 : polR, resultant : R) ==
       s : R := LC(Q)^(degree(P) - degree(Q))::NNI
       VP : Vector(polR) := [Q, 0@polR, 1@polR]
       pdiv := pseudoDivide(P, -Q)
       VQ : Vector(polR) := [pdiv.remainder, pdiv.coef::polR, pdiv.quotient]
       repeat
          --  VP.1 = S__{c-1},  VQ.1 = S__{d-1},  s=lc(S__d)
          --  S__{c-1} = VP.2 P__0 + VP.3 Q__0,  S__{d-1} = VQ.2 P__0 + VQ.3 Q__0
          (P, Q) := (VP.1, VQ.1)
          zero?(Q) => return construct(0@polR, 0@polR, 0@R)
          e : NNI := degree(Q)
          delta : NNI := (degree(P) - e)::NNI
          if zero?(e) then
             l : Vector(polR) := Lazard3(VQ, LC(Q), s, delta)
             return construct(l.2, l.3, LC(l.1))
          ss : R := Lazard(LC(Q), s, delta)
          (VP, VQ) := (VQ, next__sousResultant3(VP, VQ, s, ss))
          s := ss

    resultantEuclidean(P : polR, Q : polR) :
                       Record(coef1 : polR, coef2 : polR, resultant : R) ==
       zero?(P) or zero?(Q) => construct(0@polR, 0@polR, 0@R)
       if degree(P) < degree(Q) then
          e : Integer := if odd?(degree(P)) and odd?(degree(Q)) then -1 else 1
          l := resultantEuclidean(Q, e * P)
          return construct(e * l.coef2, l.coef1, l.resultant)
       if zero?(degree(Q)) then
          degP : NNI := degree(P)
          zero?(degP) => error("resultantEuclidean$PRS : constant polynomials")
          s : R := LC(Q)^(degP-1)::NNI
          return construct(0@polR, s::polR, s * LC(Q))
       R has Finite => resultantEuclidean__naif(P, Q)
       return subResultantEuclidean(P,Q)

    semiSubResultantEuclidean(P : polR, Q : polR) :
                       Record(coef2 : polR, resultant : R) ==
       s : R := LC(Q)^(degree(P) - degree(Q))::NNI
       VP : Vector(polR) := [Q, 1@polR]
       pdiv := pseudoDivide(P, -Q)
       VQ : Vector(polR) := [pdiv.remainder, pdiv.quotient]
       repeat
          --  VP.1 = S__{c-1},  VQ.1 = S__{d-1},  s=lc(S__d)
          --  S__{c-1} = ...P__0 + VP.3 Q__0,  S__{d-1} = ...P__0 + VQ.3 Q__0
          (P, Q) := (VP.1, VQ.1)
          zero?(Q) => return construct(0@polR, 0@R)
          e : NNI := degree(Q)
          delta : NNI := (degree(P) - e)::NNI
          if zero?(e) then
             l : Vector(polR) := Lazard3(VQ, LC(Q), s, delta)
             return construct(l.2, LC(l.1))
          ss : R := Lazard(LC(Q), s, delta)
          (VP, VQ) := (VQ, next__sousResultant3(VP, VQ, s, ss))
          s := ss

    semiResultantEuclidean2(P : polR, Q : polR) :
                       Record(coef2 : polR, resultant : R) ==
       zero?(P) or zero?(Q) => construct(0@polR, 0@R)
       degree(P) < degree(Q) => error("semiResultantEuclidean2 : bad degrees")
       if zero?(degree(Q)) then
          degP : NNI := degree(P)
          zero?(degP) => error("semiResultantEuclidean2 : constant polynomials")
          s : R := LC(Q)^(degP-1)::NNI
          return construct(s::polR, s * LC(Q))
       R has Finite => semiResultantEuclidean__naif(P, Q)
       return semiSubResultantEuclidean(P,Q)

    semiResultantEuclidean1(P : polR, Q : polR) :
                       Record(coef1 : polR, resultant : R) ==
       result := resultantEuclidean(P,Q)
       [result.coef1, result.resultant]

    indiceSubResultant(P : polR, Q : polR, i : NNI) : polR ==
       import from Integer
       zero?(Q) or zero?(P) => 0
       if degree(P) < degree(Q) then
          (P, Q) := (Q, P)
          if odd?(degree(P)-i) and odd?(degree(Q)-i) then Q := - Q
       if i = degree(Q) then
          delta : NNI := (degree(P)-degree(Q))::NNI
          zero?(delta) => error("indiceSubResultant$PRS : bad degrees")
          s : R := LC(Q)^(delta-1)::NNI
          return s*Q
       i > degree(Q) => 0
       s : R := LC(Q)^(degree(P) - degree(Q))::NNI
       (P, Q) := (Q, pseudoRemainder(P, -Q))
       repeat
          -- P = S__{c-1} ~ S__d , Q = S__{d-1},  s = lc(S__d),  i < d
          (degP, degQ) := (degree(P), degree(Q))
          i = (degP-1)::NNI => return Q
          zero?(Q) or (i > degQ) => return 0
          Z : polR := Lazard2(Q, LC(Q), s, (degP - degQ)::NNI)
          --  Z = S__e ~ S__d-1
          i = degQ => return Z
          (P, Q) := (Q, next__sousResultant2(P, Q, Z, s))
          s := LC(Z)

    indiceSubResultantEuclidean(P : polR, Q : polR, i : NNI) :
                    Record(coef1 : polR, coef2 : polR, subResultant : polR) ==
       import from Integer
       zero?(Q) or zero?(P) => construct(0@polR, 0@polR, 0@polR)
       if degree(P) < degree(Q) then
          e := if odd?(degree(P)-i) and odd?(degree(Q)-i) then -1@Integer else 1
          l := indiceSubResultantEuclidean(Q, e * P, i)
          return construct(e * l.coef2, l.coef1, l.subResultant)
       if i = degree(Q) then
          delta : NNI := (degree(P)-degree(Q))::NNI
          zero?(delta) =>
                      error("indiceSubResultantEuclidean$PRS : bad degrees")
          s : R := LC(Q)^(delta-1)::NNI
          return construct(0@polR, s::polR, s * Q)
       i > degree(Q) => construct(0@polR, 0@polR, 0@polR)
       s : R := LC(Q)^(degree(P) - degree(Q))::NNI
       VP : Vector(polR) := [Q, 0@polR, 1@polR]
       pdiv := pseudoDivide(P, -Q)
       VQ : Vector(polR) := [pdiv.remainder, pdiv.coef::polR, pdiv.quotient]
       repeat
          --  VP.1 = S__{c-1},  VQ.1 = S__{d-1},  s=lc(S__d),  i < d
          --  S__{c-1} = VP.2 P__0 + VP.3 Q__0,  S__{d-1} = VQ.2 P__0 + VQ.3 Q__0
          (P, Q) := (VP.1, VQ.1)
          zero?(Q) => return construct(0@polR, 0@polR, 0@polR)
          (degP, degQ) := (degree(P), degree(Q))
          i = (degP-1)::NNI => return construct(VQ.2, VQ.3, VQ.1)
          (i > degQ) => return construct(0@polR, 0@polR, 0@polR)
          VZ := Lazard3(VQ, LC(Q), s, (degP - degQ)::NNI)
          i = degQ => return construct(VZ.2, VZ.3, VZ.1)
          ss : R := LC(VZ.1)
          (VP, VQ) := (VQ, next__sousResultant3(VP, VQ, s, ss))
          s := ss

    local construct(coef2 : polR, subResultant : polR): Record(coef2 : polR, subResultant : polR) == [coef2, subResultant]

    semiIndiceSubResultantEuclidean(P : polR, Q : polR, i : NNI) :
                    Record(coef2 : polR, subResultant : polR) ==
       zero?(Q) or zero?(P) => construct(0@polR, 0@polR)
       degree(P) < degree(Q) =>
                  error("semiIndiceSubResultantEuclidean$PRS : bad degrees")
       if i = degree(Q) then
          delta : NNI := (degree(P)-degree(Q))::NNI
          zero?(delta) =>
                  error("semiIndiceSubResultantEuclidean$PRS : bad degrees")
          s : R := LC(Q)^(delta-1)::NNI
          return construct(s::polR, s * Q)
       i > degree(Q) => construct(0@polR, 0@polR)
       s : R := LC(Q)^(degree(P) - degree(Q))::NNI
       VP : Vector(polR) := [Q, 1@polR]
       pdiv := pseudoDivide(P, -Q)
       VQ : Vector(polR) := [pdiv.remainder, pdiv.quotient]
       repeat
          --  VP.1 = S__{c-1},  VQ.1 = S__{d-1},  s = lc(S__d),  i < d
          --  S__{c-1} = ...P__0 + VP.2 Q__0,  S__{d-1} = ...P__0 + ...Q__0
          (P, Q) := (VP.1, VQ.1)
          zero?(Q) => return construct(0@polR, 0@polR)
          (degP, degQ) := (degree(P), degree(Q))
          i = (degP-1)::NNI => return construct(VQ.2, VQ.1)
          (i > degQ) => return construct(0@polR, 0@polR)
          VZ := Lazard3(VQ, LC(Q), s, (degP - degQ)::NNI)
          i = degQ => return construct(VZ.2, VZ.1)
          ss : R := LC(VZ.1)
          (VP, VQ) := (VQ, next__sousResultant3(VP, VQ, s, ss))
          s := ss

    degreeSubResultant(P : polR, Q : polR, i : NNI) : polR ==
       zero?(Q) or zero?(P) => 0
       if degree(P) < degree(Q) then (P, Q) := (Q, P)
       if i = degree(Q) then
          delta : NNI := (degree(P)-degree(Q))::NNI
          zero?(delta) => error("degreeSubResultant$PRS : bad degrees")
          s : R := LC(Q)^(delta-1)::NNI
          return s*Q
       i > degree(Q) => 0
       s : R := LC(Q)^(degree(P) - degree(Q))::NNI
       (P, Q) := (Q, pseudoRemainder(P, -Q))
       repeat
          -- P = S__{c-1},  Q = S__{d-1},  s = lc(S__d)
          zero?(Q) or (i > degree(Q)) => return 0
          i = degree(Q) => return Q
          Z : polR := Lazard2(Q, LC(Q), s, (degree(P) - degree(Q))::NNI)
          --  Z = S__e ~ S__d-1
          (P, Q) := (Q, next__sousResultant2(P, Q, Z, s))
          s := LC(Z)

    degreeSubResultantEuclidean(P : polR, Q : polR, i : NNI) :
                     Record(coef1 : polR, coef2 : polR, subResultant : polR) ==
       zero?(Q) or zero?(P) => construct(0@polR, 0@polR, 0@polR)
       if degree(P) < degree(Q) then
          l := degreeSubResultantEuclidean(Q, P, i)
          return construct(l.coef2, l.coef1, l.subResultant)
       if i = degree(Q) then
          delta : NNI := (degree(P)-degree(Q))::NNI
          zero?(delta) =>
                      error("degreeSubResultantEuclidean$PRS : bad degrees")
          s : R := LC(Q)^(delta-1)::NNI
          return construct(0@polR, s::polR, s * Q)
       i > degree(Q) => construct(0@polR, 0@polR, 0@polR)
       s : R := LC(Q)^(degree(P) - degree(Q))::NNI
       VP : Vector(polR) := [Q, 0@polR, 1@polR]
       pdiv := pseudoDivide(P, -Q)
       VQ : Vector(polR) := [pdiv.remainder, pdiv.coef::polR, pdiv.quotient]
       repeat
          --  VP.1 = S__{c-1},  VQ.1 = S__{d-1},  s=lc(S__d)
          --  S__{c-1} = ...P__0 + VP.3 Q__0,  S__{d-1} = ...P__0 + VQ.3 Q__0
          (P, Q) := (VP.1, VQ.1)
          zero?(Q) or (i > degree(Q)) =>
               return construct(0@polR, 0@polR, 0@polR)
          i = degree(Q) => return construct(VQ.2, VQ.3, VQ.1)
          ss : R := Lazard(LC(Q), s, (degree(P)-degree(Q))::NNI)
          (VP, VQ) := (VQ, next__sousResultant3(VP, VQ, s, ss))
          s := ss

    semiDegreeSubResultantEuclidean(P : polR, Q : polR, i : NNI) :
                     Record(coef2 : polR, subResultant : polR) ==
       zero?(Q) or zero?(P) => construct(0@polR, 0@polR)
       degree(P) < degree(Q) =>
                  error("semiDegreeSubResultantEuclidean$PRS : bad degrees")
       if i = degree(Q) then
          delta : NNI := (degree(P)-degree(Q))::NNI
          zero?(delta) =>
                  error("semiDegreeSubResultantEuclidean$PRS : bad degrees")
          s : R := LC(Q)^(delta-1)::NNI
          return construct(s::polR, s * Q)
       i > degree(Q) => construct(0@polR, 0@polR)
       s : R := LC(Q)^(degree(P) - degree(Q))::NNI
       VP : Vector(polR) := [Q, 1@polR]
       pdiv := pseudoDivide(P, -Q)
       VQ : Vector(polR) := [pdiv.remainder, pdiv.quotient]
       repeat
          --  VP.1 = S__{c-1},  VQ.1 = S__{d-1},  s=lc(S__d)
          --  S__{c-1} = ...P__0 + VP.3 Q__0,  S__{d-1} = ...P__0 + VQ.3 Q__0
          (P, Q) := (VP.1, VQ.1)
          zero?(Q) or (i > degree(Q)) =>
               return construct(0@polR, 0@polR)
          i = degree(Q) => return construct(VQ.2, VQ.1)
          ss : R := Lazard(LC(Q), s, (degree(P)-degree(Q))::NNI)
          (VP, VQ) := (VQ, next__sousResultant3(VP, VQ, s, ss))
          s := ss

    lastSubResultant(P : polR, Q : polR) : polR ==
       zero?(Q) or zero?(P) => 0
       if degree(P) < degree(Q) then (P, Q) := (Q, P)
       zero?(degree(Q)) => (LC(Q)^degree(P))::polR
       s : R := LC(Q)^(degree(P) - degree(Q))::NNI
       (P, Q) := (Q, pseudoRemainder(P, -Q))
       Z : polR := P
       repeat
          -- Z = S__d  (except the first turn : Z = P)
          -- P = S__{c-1} ~ S__d,  Q = S__{d-1},  s = lc(S__d)
          zero?(Q) => return Z
          Z := Lazard2(Q, LC(Q), s, (degree(P) - degree(Q))::NNI)
          -- Z = S__e ~ S__{d-1}
          zero?(degree(Z)) => return Z
          (P, Q) := (Q, next__sousResultant2(P, Q, Z, s))
          s := LC(Z)

    lastSubResultantEuclidean(P : polR, Q : polR) :
                    Record(coef1 : polR, coef2 : polR, subResultant : polR) ==
       zero?(Q) or zero?(P) => construct(0@polR, 0@polR, 0@polR)
       if degree(P) < degree(Q) then
          l := lastSubResultantEuclidean(Q, P)
          return construct(l.coef2, l.coef1, l.subResultant)
       if zero?(degree(Q)) then
          degP : NNI := degree(P)
          zero?(degP) =>
              error("lastSubResultantEuclidean$PRS : constant polynomials")
          s : R := LC(Q)^(degP-1)::NNI
          return construct(0@polR, s::polR, s * Q)
       s : R := LC(Q)^(degree(P) - degree(Q))::NNI
       VP : Vector(polR) := [Q, 0@polR, 1@polR]
       pdiv := pseudoDivide(P, -Q)
       VQ : Vector(polR) := [pdiv.remainder, pdiv.coef::polR, pdiv.quotient]
       VZ : Vector(polR) := copy(VP)
       repeat
          --  VZ.1 = S__d,  VP.1 = S__{c-1},  VQ.1 = S__{d-1},  s = lc(S__d)
          --  S__{c-1} = VP.2 P__0 + VP.3 Q__0
          --  S__{d-1} = VQ.2 P__0 + VQ.3 Q__0
          --  S__d     = VZ.2 P__0 + VZ.3 Q__0
          (Q, Z) := (VQ.1, VZ.1)
          zero?(Q) => return construct(VZ.2, VZ.3, VZ.1)
          VZ := Lazard3(VQ, LC(Q), s, (degree(Z) - degree(Q))::NNI)
          zero?(degree(Q)) => return construct(VZ.2, VZ.3, VZ.1)
          ss : R := LC(VZ.1)
          (VP, VQ) := (VQ, next__sousResultant3(VP, VQ, s, ss))
          s := ss

    semiLastSubResultantEuclidean(P : polR, Q : polR) :
                    Record(coef2 : polR, subResultant : polR) ==
       zero?(Q) or zero?(P) => construct(0@polR, 0@polR)
       degree(P) < degree(Q) =>
              error("semiLastSubResultantEuclidean$PRS : bad degrees")
       if zero?(degree(Q)) then
          degP : NNI := degree(P)
          zero?(degP) =>
              error("semiLastSubResultantEuclidean$PRS : constant polynomials")
          s : R := LC(Q)^(degP-1)::NNI
          return construct(s::polR, s * Q)
       s : R := LC(Q)^(degree(P) - degree(Q))::NNI
       VP : Vector(polR) := [Q, 1@polR]
       pdiv := pseudoDivide(P, -Q)
       VQ : Vector(polR) := [pdiv.remainder, pdiv.quotient]
       VZ : Vector(polR) := copy(VP)
       repeat
          --  VZ.1 = S__d,  VP.1 = S__{c-1},  VQ.1 = S__{d-1},  s = lc(S__d)
          --  S__{c-1} = ... P__0 + VP.2 Q__0
          --  S__{d-1} = ... P__0 + VQ.2 Q__0
          --  S__d     = ... P__0 + VZ.2 Q__0
          (Q, Z) := (VQ.1, VZ.1)
          zero?(Q) => return construct(VZ.2, VZ.1)
          VZ := Lazard3(VQ, LC(Q), s, (degree(Z) - degree(Q))::NNI)
          zero?(degree(Q)) => return construct(VZ.2, VZ.1)
          ss : R := LC(VZ.1)
          (VP, VQ) := (VQ, next__sousResultant3(VP, VQ, s, ss))
          s := ss

    chainSubResultants(P : polR, Q : polR) : List(polR) ==
       import from NonNegativeInteger
       zero?(Q) or zero?(P) => []
       if degree(P) < degree(Q) then
          (P, Q) := (Q, P)
          if odd?(degree(P)) and odd?(degree(Q)) then Q := - Q
       L : List(polR) := []
       zero?(degree(Q)) => L
       L := [Q]
       s : R := LC(Q)^(degree(P) - degree(Q))::NNI
       (P, Q) := (Q, pseudoRemainder(P, -Q))
       repeat
          -- P = S__{c-1},  Q = S__{d-1},  s = lc(S__d)
          -- L = [S__d,....,S__{q-1}]
          zero?(Q) => return L
          L := concat(Q, L)
          -- L = [S__{d-1},....,S__{q-1}]
          delta : NNI := (degree(P) - degree(Q))::NNI
          Z : polR := Lazard2(Q, LC(Q), s, delta)            -- Z = S__e ~ S__d-1
          if delta > 1 then L := concat(Z, L)
          -- L = [S__e,....,S__{q-1}]
          zero?(degree(Z)) => return L
          (P, Q) := (Q, next__sousResultant2(P, Q, Z, s))
          s := LC(Z)

    schema(P : polR, Q : polR) : List(NNI) ==
       zero?(Q) or zero?(P) => []
       if degree(P) < degree(Q) then (P, Q) := (Q, P)
       zero?(degree(Q)) => [0]
       L : List(NNI) := []
       s : R := LC(Q)^(degree(P) - degree(Q))::NNI
       (P, Q) := (Q, pseudoRemainder(P, Q))
       repeat
          -- P = S__{c-1} ~ S__d,  Q = S__{d-1},  s = lc(S__d)
          zero?(Q) => return L
          e : NNI := degree(Q)
          L := concat(e, L)
          delta : NNI := (degree(P) - e)::NNI
          Z : polR := Lazard2(Q, LC(Q), s, delta)            -- Z = S__e ~ S__d-1
          if delta > 1 then L := concat(e, L)
          zero?(e) => return L
          (P, Q) := (Q, next__sousResultant2(P, Q, Z, s))
          s := LC(Z)

    subResultantGcd(P : polR, Q : polR) : polR ==
       zero?(P) and zero?(Q) => 0
       zero?(P) => Q
       zero?(Q) => P
       if degree(P) < degree(Q) then (P, Q) := (Q, P)
       zero?(degree(Q)) => 1$polR
       s : R := LC(Q)^(degree(P) - degree(Q))::NNI
       (P, Q) := (Q, pseudoRemainder(P, -Q))
       repeat
          -- P = S__{c-1},  Q = S__{d-1},  s = lc(S__d)
          zero?(Q) => return P
          zero?(degree(Q)) => return 1$polR
          Z : polR := Lazard2(Q, LC(Q), s, (degree(P) - degree(Q))::NNI)
          -- Z = S__e ~ S__d-1
          (P, Q) := (Q, next__sousResultant2(P, Q, Z, s))
          s := LC(Z)

    construct(coef1 : polR, coef2 : polR, gcd : polR): Record(coef1 : polR, coef2 : polR, gcd : polR) == [coef1, coef2, gcd]

    subResultantGcdEuclidean(P : polR, Q : polR) :
                    Record(coef1 : polR, coef2 : polR, gcd : polR) ==
       zero?(P) and zero?(Q) => construct(0@polR, 0@polR, 0@polR)
       zero?(P) => construct(0@polR, 1@polR, Q)
       zero?(Q) => construct(1@polR, 0@polR, P)
       if degree(P) < degree(Q) then
          l := subResultantGcdEuclidean(Q, P)
          return construct(l.coef2, l.coef1, l.gcd)
       zero?(degree(Q)) => construct(0@polR, 1@polR, Q)
       s : R := LC(Q)^(degree(P) - degree(Q))::NNI
       VP : Vector(polR) := [Q, 0@polR, 1@polR]
       pdiv := pseudoDivide(P, -Q)
       VQ : Vector(polR) := [pdiv.remainder, pdiv.coef::polR, pdiv.quotient]
       repeat
          --  VP.1 = S__{c-1},  VQ.1 = S__{d-1},  s=lc(S__d)
          --  S__{c-1} = VP.2 P__0 + VP.3 Q__0,  S__{d-1} = VQ.2 P__0 + VQ.3 Q__0
          (P, Q) := (VP.1, VQ.1)
          zero?(Q) => return construct(VP.2, VP.3, P)
          e : NNI := degree(Q)
          zero?(e) => return construct(VQ.2, VQ.3, Q)
          ss := Lazard(LC(Q), s, (degree(P) - e)::NNI)
          (VP,VQ) := (VQ, next__sousResultant3(VP, VQ, s, ss))
          s := ss

    local construct(coef2 : polR, gcd : polR): Record(coef2 : polR, gcd : polR) == [coef2, gcd]

    semiSubResultantGcdEuclidean2(P : polR, Q : polR) :
                                  Record(coef2 : polR, gcd : polR) ==
       zero?(P) and zero?(Q) => construct(0@polR, 0@polR)
       zero?(P) => construct(1@polR, Q)
       zero?(Q) => construct(0@polR, P)
       degree(P) < degree(Q) =>
                       error("semiSubResultantGcdEuclidean2$PRS : bad degrees")
       zero?(degree(Q)) => construct(1@polR, Q)
       s : R := LC(Q)^(degree(P) - degree(Q))::NNI
       VP : Vector(polR) := [Q, 1@polR]
       pdiv := pseudoDivide(P, -Q)
       VQ : Vector(polR) := [pdiv.remainder, pdiv.quotient]
       repeat
          --  P=S__{c-1},  Q=S__{d-1},  s=lc(S__d)
          --  S__{c-1} = ? P__0 + old__cf2 Q__0,  S__{d-1} = ? P__0 + cf2 Q__0
          (P, Q) := (VP.1, VQ.1)
          zero?(Q) => return construct(VP.2, P)
          e : NNI := degree(Q)
          zero?(e) => return construct(VQ.2, Q)
          ss := Lazard(LC(Q), s, (degree(P) - e)::NNI)
          (VP,VQ) := (VQ, next__sousResultant3(VP, VQ, s, ss))
          s := ss

    construct(coef1: polR, gcd: polR): Record(coef1 : polR, gcd : polR) == [coef1, gcd]

    semiSubResultantGcdEuclidean1(P : polR, Q : polR) :
                       Record(coef1 : polR, gcd : polR) ==
       import from Record(coef1: polR, coef2: polR, gcd: polR)
       result := subResultantGcdEuclidean(P,Q)
       [result.coef1, result.gcd]

    discriminant(P : polR) : R ==
       d : Integer := degree(P)::Integer
       zero?(d) => error "cannot take discriminant of constants"
       a : Integer := (d * (d-1)) quo 2
       a := (-1)^a::NonNegativeInteger
       dP : polR := differentiate P
       r : R := resultant(P, dP)
       d := d - degree(dP)::Integer - 1
       return (if zero?(d) then a * (r exquo LC(P))::R
               else a * r * LC(P)^(d-1)::NNI)

    construct(coef1 : polR, coef2 : polR, discriminant : R): Record(coef1 : polR, coef2 : polR, discriminant : R) == [coef1, coef2, discriminant]

    discriminantEuclidean(P : polR) :
                       Record(coef1 : polR, coef2 : polR, discriminant : R) ==
       d : Integer := degree(P)::Integer
       zero?(d) => error "cannot take discriminant of constants"
       a : Integer := (d * (d-1)) quo 2
       a := (-1)^a::NonNegativeInteger
       dP : polR := differentiate P
       rE := resultantEuclidean(P, dP)
       d := d - degree(dP)::Integer - 1
       if zero?(d) then
          c1 : polR := a * (rE.coef1 exquo LC(P))::polR
          c2 : polR := a * (rE.coef2 exquo LC(P))::polR
          cr : R := a * (rE.resultant exquo LC(P))::R
       else
          c1 : polR := a * rE.coef1 * LC(P)^(d-1)::NNI
          c2 : polR := a * rE.coef2 * LC(P)^(d-1)::NNI
          cr : R := a * rE.resultant * LC(P)^(d-1)::NNI
       return construct(c1, c2, cr)

    construct(coef2: polR, discriminant: R): Record(coef2 : polR, discriminant : R) == [coef2, discriminant]

    semiDiscriminantEuclidean(P : polR) :
                            Record(coef2 : polR, discriminant : R) ==
       d : Integer := degree(P)::Integer
       zero?(d) => error "cannot take discriminant of constants"
       a : Integer := (d * (d-1)) quo 2
       a := (-1)^a::NonNegativeInteger
       dP : polR := differentiate P
       rE := semiResultantEuclidean2(P, dP)
       d := d - degree(dP)::Integer - 1
       if zero?(d) then
          c2 : polR := a * (rE.coef2 exquo LC(P))::polR
          cr : R := a * (rE.resultant exquo LC(P))::R
       else
          c2 : polR := a * rE.coef2 * LC(P)^(d-1)::NNI
          cr : R := a * rE.resultant * LC(P)^(d-1)::NNI
       return construct(c2, cr)

    if R has GcdDomain0 then
       resultantReduit(P : polR, Q : polR) : R ==
          import from Record(coef1 : polR, coef2 : polR, gcd : polR)
          UV := subResultantGcdEuclidean(P, Q)
          UVs : polR := UV.gcd
          degree(UVs) > 0 => 0
          l : List(R) := concat(coefficients(UV.coef1), coefficients(UV.coef2))
          return (LC(UVs) exquo gcd(l))::R

       construct(coef1 : polR, coef2 : polR, resultantReduit : R): Record(coef1 : polR, coef2 : polR, resultantReduit : R) == [coef1, coef2, resultantReduit]

       resultantReduitEuclidean(P : polR, Q : polR) :
                     Record(coef1 : polR, coef2 : polR, resultantReduit : R) ==
          import from Record(coef1 : polR, coef2 : polR, gcd : polR)
          UV := subResultantGcdEuclidean(P, Q)
          UVs : polR := UV.gcd
          degree(UVs) > 0 => construct(0@polR, 0@polR, 0@R)
          l : List(R) := concat(coefficients(UV.coef1), coefficients(UV.coef2))
          gl : R := gcd(l)
          c1 : polR := (UV.coef1 exquo gl)::polR
          c2 : polR := (UV.coef2 exquo gl)::polR
          rr : R := (LC(UVs) exquo gl)::R
          return construct(c1, c2, rr)

       construct(coef2 : polR, resultantReduit : R): Record(coef2 : polR, resultantReduit : R) == [coef2, resultantReduit]
       semiResultantReduitEuclidean(P : polR, Q : polR) :
                                   Record(coef2 : polR, resultantReduit : R) ==
          import from Record(coef1 : polR, coef2 : polR, gcd : polR)
          UV := subResultantGcdEuclidean(P, Q)
          UVs : polR := UV.gcd
          degree(UVs) > 0 => construct(0@polR, 0@R)
          l : List(R) := concat(coefficients(UV.coef1), coefficients(UV.coef2))
          gl : R := gcd(l)
          c2 : polR := (UV.coef2 exquo gl)::polR
          rr : R := (LC(UVs) exquo gl)::R
          return construct(c2, rr)

       gcd__naif(P : polR, Q : polR) : polR ==
       -- valid over a field
          zero?(P) => (Q exquo LC(Q))::polR
          repeat
             zero?(Q) => return (P exquo LC(P))::polR
             zero?(degree(Q)) => return 1$polR
             (P, Q) := (Q, divide(P, Q).remainder)

       gcd(P : polR, Q : polR) : polR ==
          R has Finite => gcd__naif(P,Q)
          zero?(P) => Q
          zero?(Q) => P
          cP : R := content(P)
          cQ : R := content(Q)
          P := (P exquo cP)::polR
          Q := (Q exquo cQ)::polR
          G : polR := subResultantGcd(P, Q)
          return gcd(cP,cQ) * primitivePart(G)
