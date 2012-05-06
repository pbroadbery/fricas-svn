--DEPS: IntegralDomain List Set
#include "axiom"
#pile

import from String;

Factored(R: IntegralDomain): Exports == Implementation where
  fUnion ==> ('nil,sqfr,irred,prime')
  FF     ==> Record(flg: fUnion, fctr: R, xpnt: Integer)
  SRFE   ==> Set RFE R
  Exports ==> with
    SetCategory
    unit:    % -> R
      ++ unit(u) extracts the unit part of the factorization.
    factors: % -> List RFE(R)
      ++ factors(u) returns a list of the factors in a form suitable
      ++ for iteration. That is, it returns a list where each element
      ++ is a record containing a base and exponent.  The original
      ++ object is the product of all the factors and the unit (which
      ++ can be extracted by \axiom{unit(u)}).
    factorList : % -> List FF
      ++ factorList(u) returns the list of factors with flags (for
      ++ use by factoring code).
  Implementation ==> add
    Rep == Record(unt:R, fct:List FF)
    import from NonNegativeInteger
    import from Rep
    import from FF
    default u: %
    
    local apply(u: %, zz: 'unt'): R == rep(u).unt
    local apply(u: %, zz: 'fct'): List FF == rep(u).fct
    local [a: R, fct: List FF]: % == per [a, fct]

    factorList u: List FF == rep(u).fct
    factors u: List RFE R == [[fe.fctr, fe.xpnt] for fe in factorList u]
    unit u: R == rep(u).unt

    (u: %) = (v: %): Boolean ==
      (unit u = unit v) and # u.fct = # v.fct and
        set(factors u)$SRFE =$SRFE set(factors v)$SRFE

    coerce(x:%): OutputForm ==
      import from List OutputForm
      empty?(lf := reverse factorList x) => (unit x)::OutputForm
      l := empty()$List(OutputForm)
      for rec in lf repeat
        ((rec.fctr) = 1) => messagePrint "WARNING (coerce$Factored): 1 should not appear as factor."
        ((rec.xpnt) = 1) =>
          l := concat(rec.fctr :: OutputForm, l)
        l := concat(rec.fctr::OutputForm ^ rec.xpnt::OutputForm, l)
      empty? l => (unit x) :: OutputForm
      e :=
        empty? rest l => first l
        reduce(_*, l)
      1 = unit x => e
      (unit x)::OutputForm * e



-- Records are not of SetCategory.  We could extend them so that they
-- are, but we'll not do it just for this one case

RFE(R: SetCategory): SetCategory with 
   bracket: (R, Integer) -> %
   apply: (%, 'factor') -> R
   apply: (%, 'exponent') -> Integer
   export from 'factor', 'exponent'
== add
   Rep ==> Record(factor: R, exponent: Integer)
   import from Rep
   [r: R, e: Integer]: % == per [r, e]

   apply(a: %, f: 'factor'): R == rep(a).factor   
   apply(a: %, f: 'exponent'): Integer == rep(a).exponent

   (a: %) = (b: %): Boolean == a.factor = b.factor and a.exponent = b.exponent
   coerce(a: %): OutputForm == never
