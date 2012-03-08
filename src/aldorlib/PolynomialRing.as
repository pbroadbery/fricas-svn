--DEPS: FreeModule FiniteAbelianMonoidRing IntegralDomain canonicalUnitNormal Field0 Integer_IntegralDomain
--DEPS: Approximate
#include "axiom.as"
#pile

import from Boolean
import from System
import from String

PolynomialRing(R : Join(SemiRng, AbelianMonoid), E : OrderedAbelianMonoid
              ) : FiniteAbelianMonoidRing(R,E) with
    --assertions
       if R has IntegralDomain and E has CancellationAbelianMonoid then
            fmecg: (%,E,R,%) -> %
              ++ fmecg(p1,e,r,p2) finds X : p1 - r * X^e * p2
       if R has canonicalUnitNormal then canonicalUnitNormal
          -- canonicalUnitNormal guarantees that the function
          -- unitCanonical returns the same representative for all
          -- associates of any particular element.
       if R has Comparable then Comparable

==  FreeModule(R,E) add
    --representations
       Term ==>  Record(k:E,c:R)
       Rep ==  List Term

       TermS ==>  Record(k : SingleInteger, c : R)
       RepS ==> List TermS
       import from Term
       import from List Term
       import from E, R
       import from Rep

    --declarations
       default x,y,p,p1,p2: %
       default n: Integer
       default nn: NonNegativeInteger
       default np: PositiveInteger
       default e: E
       default r: R

       local null(x: %): Boolean == null rep(x)
       local empty?(x: %): Boolean == null rep(x)
       local apply(x: %, zz: 'first'): Term == (rep x).first
       local apply(x: %, zz: 'rest'): % == per [a for a in (rep x).rest]
       local first(x: %): Term == x.first
       local rest(x: %): % == x.rest
       local cons(t: Term, p: %): % == per cons(t, rep p)

       commutative: Boolean == R has CommutativeRing

    --local operations
       if R has Monoid then -- Was "AbelianMonoid".. clearly not right.
           1: %  == monomial(1$R, 0)
           sample(): % == monomial(1$R, 0)
       if R has Ring then
           characteristic(): NonNegativeInteger  == characteristic()$R
       numberOfMonomials x: NonNegativeInteger  == (# rep x)$Rep
       degree p: E == if null p then 0 else p.first.k
       minimumDegree p: E == if null p then 0 else (last rep p).k
       leadingCoefficient p: R == if null p then 0$R else p.first.c
       leadingMonomial p: % == if null p then 0$% else per [p.first]
       reductum p: % == if null p then p else p.rest
       retractIfCan(p:%): Partial R ==
         null p => success(0$R)
         not null p.rest => failed()
         zero?(p.first.k) => success(p.first.c)
         failed()

       coefficient(p : %, e : E): R  ==
               for tm in rep p repeat
                   tm.k=e => return tm.c
                   tm.k < e => return 0$R
               0$R

       if R has Monoid then -- Was unconditional, but need R to have recip
         recip(p): Partial % ==
           import from Partial R
           null p => failed()
           p.first.k > 0$E => failed()
           failed?(u:=recip(p.first.c)) => failed()
           success(monomial(u::R, 0))

       coerce(r): % == if zero? r then 0$% else monomial(r, 0)
       if R has Ring then
           coerce(n): % == (n::R)::%

       ground?(p): Boolean == empty? p or (empty? rest p and zero? degree p)

       -- qsetrest!: (Rep, Rep) -> Rep
       -- qsetrest!(l: Rep, e: Rep): Rep == RPLACD(l, e)$Lisp
       --qsetrest! ==> RPLACD$Lisp
       local qsetrest!(l: Rep, newrest: Rep): () == l.rest := newrest;

       times!: (R,    %) -> %
       times:  (R, E, %) -> %

       entireRing?: Boolean == R has noZeroDivisors

       times!(r: R, x: %): % ==
         local res, endcell, newend, xx: Rep
         if entireRing? then
                for tx in rep(x) repeat tx.c := r*tx.c
                x
         else
                xx := rep x
                res := empty()
                while not empty? xx repeat
                        tx := first xx
                        tx.c := r * tx.c
                        if zero? tx.c then
                                xx := rest xx
                        else
                                newend := xx
                                xx := rest xx
                                if empty? res then
                                        res := newend
                                        endcell := res
                                else
                                        qsetrest!(endcell, newend)
                                        endcell := newend
                per res

        --- term * polynomial
       termTimes: (R, E, Term) -> Term
       termTimes(r: R, e: E, tx:Term): Term == [e+tx.k, r*tx.c]
       times(tco: R, tex: E, rx: %): % ==
        if entireRing? then
                per map((x1: Term): Term +-> termTimes(tco, tex, x1), rep rx)
        else
                per [[tex + tx.k, r] for tx in rep(rx) | not zero? (r := tco * tx.c)]



       -- local addm!
       addm!: (Rep, R, E, Rep) -> Rep
        -- p1 + coef*x^E * p2
        -- `spare' (commented out) is for storage efficiency (not so good for
        -- performance though.
       ADDM__BODY ==>
                res     := empty()
                endcell := empty()
                --spare   := empty()
                while not empty? pp1 and not empty? pp2 repeat
                        tx := first pp1
                        ty := first pp2
                        exy := exp + ty.k
                        newcell := empty()
                        if tx.k = exy then
                                newcoef := tx.c + coef * ty.c
                                if not zero? newcoef then
                                        tx.c    := newcoef
                                        newcell := pp1
                                --else
                                --      spare   := cons(pp1, spare)
                                pp1 := rest pp1
                                pp2 := rest pp2
                        else if exy < tx.k then
                                newcell := pp1
                                pp1      := rest pp1
                        else
                                newcoef := coef * ty.c
                                if not entireRing? and zero? newcoef then
                                        newcell := empty()
                                --else if empty? spare then
                                --      ttt := [exy, newcoef]
                                --      newcell := cons(ttt, empty())
                                --else
                                --      newcell := first spare
                                --      spare   := rest spare
                                --      ttt := first newcell
                                --      ttt.k := exy
                                --      ttt.c := newcoef
                                else
                                        ttt := [exy, newcoef]
                                        newcell := cons(ttt, empty())
                                pp2 := rest pp2
                        if not empty? newcell then
                                if empty? res then
                                        res := newcell
                                        endcell := res
                                else
                                        qsetrest!(endcell, newcell)
                                        endcell := newcell

       addm!(pp1: Rep, coef:R, exp: E, pp2:Rep): Rep ==
           local res, newcell, endcell: Rep
	   res := newcell := endcell := empty();
           --local spare: List Rep
           ADDM__BODY
           if not empty? pp1 then  -- then end is const * pp1
               newcell := pp1
           else  -- then end is (coef, exp) * pp2
               newcell := rep times(coef, exp, per pp2)
           empty? res => newcell
           qsetrest!(endcell, newcell)
           res
      
       pomopo! (p1, r, e, p2): % ==  per addm!(rep p1, r, e, rep p2)
       
       p1 * p2: % ==
                xx := rep p1
                empty? xx => p1
                yy := rep p2
                empty? yy => p2
                zero? first(xx).k => first(xx).c * p2
                zero? first(yy).k => p1 * first(yy).c
                --if #xx > #yy then
                --      (xx, yy) := (yy, xx)
                --      (p1, p2) := (p2, p1)
                xx := reverse xx
                res : Rep := empty()
                for tx in xx repeat res:=addm!(res,tx.c,tx.k,yy)
                per res

--     if R has noZeroDivisors then
--         p1 * p2  ==
--            null p1 => 0
--            null p2 => 0
--            zero?(p1.first.k) => p1.first.c * p2
--            one? p2 => p1
--            +/[[[t1.k+t2.k,t1.c*t2.c]$Term for t2 in p2]
--                   for t1 in reverse(p1)]
--                   -- This 'reverse' is an efficiency improvement:
--                   -- reduces both time and space [Abbott/Bradford/Davenport]
--        else
--         p1 * p2  ==
--            null p1 => 0
--            null p2 => 0
--            zero?(p1.first.k) => p1.first.c * p2
--            one? p2 => p1
--            +/[[[t1.k+t2.k,r]$Term for t2 in p2 | (r:=t1.c*t2.c) ~= 0]
--                 for t1 in reverse(p1)]
--                  -- This 'reverse' is an efficiency improvement:
--                  -- reduces both time and space [Abbott/Bradford/Davenport]
       if R has CommutativeRing  then

         p ^ np: % == p ^ (np pretend NonNegativeInteger)

         p ^ nn: %  ==
            null p => 0
            zero? nn => 1
--            one? nn => p
            (nn = 1) => p
            empty? p.rest =>
              zero?(cc:=p.first.c ^ nn) => 0
              per [[nn * p.first.k, cc]]
            binomThmExpt(per [p.first], p.rest, nn)

       UCA(X) ==> Record(unit:X,canonical:X,associate:X)
       import from UCA %;
       import from UCA R;
       if R has Field0 then

         unitNormal(p): UCA %==
            null p or (lcf:R:=p.first.c) = 1 => [1,p,1]
            a := inv lcf
            [lcf::%, cons([p.first.k,1], (a * p.rest)), a::%]
         unitCanonical(p): % ==
            null p or (lcf:R:=p.first.c) = 1 => p
            a := inv lcf
            cons([p.first.k,1],(a * p.rest))
       else if R has IntegralDomain then

         unitNormal(p): UCA %==
            null p or p.first.c = 1 => [1,p,1]
            (u,cf,a):= explode unitNormal(p.first.c)
            [u::%, cons([p.first.k,cf], (a * p.rest)), a::%]

         unitCanonical(p): % ==
            null p or p.first.c = 1 => p
            (u,cf,a):=explode unitNormal(p.first.c)
            cons([p.first.k,cf], (a * p.rest))

       if R has IntegralDomain then
         associates?(p1,p2): Boolean ==
            import from Partial R
            null p1 => null p2
            null p2 => false
            p1.first.k = p2.first.k and
              associates?(p1.first.c,p2.first.c) and
               ((p2.first.c exquo p1.first.c)::R * p1.rest = p2.rest)

         p exquo r: Partial %  ==
	   import from Partial R
	   l := empty();
	   for tm in rep p repeat 
	      a := tm.c exquo r
	      if failed? a then return failed();
	      else
		l := cons([tm.k, a::R], l)
	   success per reverse! l;	
--           success per [(if failed?(a:= tm.c exquo r)
--                         then return failed() else [tm.k,a])
--                        for tm in rep p]
			  
         local nreconc!(l1: List Term, l2: List Term): List Term == concat!(reverse! l1, l2)

         if E has CancellationAbelianMonoid then
           fmecg(p1:%,e:E,r:R,p2:%):% ==       -- p1 - r * X^e * p2
	      local c2: R
              rout:%:= per []
              r:= - r
              for tm in rep p2 repeat
                 e2:= e + tm.k
                 c2:= r * tm.c
                 c2 = 0 => "next term"
                 while not null p1 and p1.first.k > e2 repeat
                   (rout:=cons(p1.first, rout); p1:=p1.rest)  --use PUSH and POP?
                 null p1 or p1.first.k < e2 => rout:=cons([e2,c2], rout)
                 if (u:=p1.first.c + c2) ~= 0 then rout:=cons([e2, u], rout)
                 p1:=p1.rest
              per nreconc!(rep rout,rep p1)

           if R has Approximate then

             p1 exquo p2: Partial %  ==
	       import from Partial R
	       import from Partial E
               null p2 => error "Division by 0"
               p2 = 1 => success(p1)
               p1=p2 => success(1)
             --(p1.lastElt.c exquo p2.lastElt.c) case "failed" => "failed"
               rout:= []@List(Term)
               while not null p1 repeat
                  (a:= p1.first.c exquo p2.first.c)
                  failed? a => return failed()
                  ee:= subtractIfCan(p1.first.k, p2.first.k)
                  failed? ee => return failed()
                  p1:= fmecg(p1.rest, ee::E, a::R, p2.rest)
                  rout:= cons([ee::E,a::R], rout)
               null p1 => success(per reverse(rout))    -- nreverse?
               failed()
           else -- R not Approximate
             p1 exquo p2: Partial %  ==
	       import from Partial R
	       import from Partial E
               null p2 => error "Division by 0"
               p2 = 1 => success p1
             --(p1.lastElt.c exquo p2.lastElt.c) case "failed" => "failed"
               rout:= []@List(Term)
               while not null p1 repeat
                  (a:= p1.first.c exquo p2.first.c)
                  failed?(a) => return failed()
                  ee:= subtractIfCan(p1.first.k, p2.first.k)
                  failed? ee => return failed()
                  p1:= fmecg(p1.rest, ee::E, a::R, p2.rest)
                  rout:= cons([ee::E, a::R], rout)
               null p1 => success(per reverse(rout))    -- nreverse?
               failed()

       if R has CharacteristicNonZero then
          charthRoot(x: %): Partial % == never

       if R has Field0 then
          x/r: % == inv(r)*x

       if R has Algebra Fraction Integer then

       	  (p1: %) * (g: Fraction Integer): % == 
	       map((r: R): R +-> r * g, p1)
