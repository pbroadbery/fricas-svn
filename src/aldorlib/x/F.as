--DEPS: Factored_Base DifferentialExtension FullyEvalableOver FullyRetractableTo
--DEPS: GcdDomain RealConstant UniqueFactorizationDomain IntegerNumberSystem0
--DEPS: Field0 IntegerFactorizationPackage Set List_ListAggregate
--DEPS: Float_Field0 DoubleFloat_Field0
#include "axiom"
#pile

import from String
import from System

-- This domain is pretty much a trainwreck.
-- It needs to decide if it's a relatively simple list of factors, or
-- a full IntegralDomain.  And even then, how it should integrate with the
-- underlying domain
(local xyzzy: with == add; extend Factored(R: IntegralDomain): Exports == Implementation) where
  fUnion ==> 'nil,sqfr,irred,prime'
  FF     ==> Record(flg: fUnion, fctr: R, xpnt: Integer)
  SRFE   ==> Set RFE R
  Exports ==> Join(IntegralDomain, DifferentialExtension R, Algebra R,
                   FullyEvalableOver R, FullyRetractableTo R) with
    expand: % -> R
      ++ expand(f) multiplies the unit and factors together, yielding an
      ++ "unfactored" object. Note: this is purposely not called \spadfun{coerce} which would
      ++ cause the interpreter to do this automatically.

    exponent:  % -> Integer
      ++ exponent(u) returns the exponent of the first factor of
      ++ \spadvar{u}, or 0 if the factored form consists solely of a unit.

    makeFR  : (R, List FF) -> %
      ++ makeFR(unit,listOfFactors) creates a factored object (for
      ++ use by factoring code).

    factorList : % -> List FF
      ++ factorList(u) returns the list of factors with flags (for
      ++ use by factoring code).

    nilFactor: (R, Integer) -> %
      ++ nilFactor(base,exponent) creates a factored object with
      ++ a single factor with no information about the kind of
      ++ base (flag = "nil").

    factors: % -> List RFE R
      ++ factors(u) returns a list of the factors in a form suitable
      ++ for iteration. That is, it returns a list where each element
      ++ is a record containing a base and exponent.  The original
      ++ object is the product of all the factors and the unit (which
      ++ can be extracted by \axiom{unit(u)}).

    irreducibleFactor: (R, Integer) -> %
      ++ irreducibleFactor(base,exponent) creates a factored object with
      ++ a single factor whose base is asserted to be irreducible
      ++ (flag = "irred").

    nthExponent: (%, Integer) -> Integer
      ++ nthExponent(u,n) returns the exponent of the nth factor of
      ++ \spadvar{u}.  If \spadvar{n} is not a valid index for a factor
      ++ (for example, less than 1 or too big), 0 is returned.

    nthFactor:  (%,Integer) -> R
      ++ nthFactor(u,n) returns the base of the nth factor of
      ++ \spadvar{u}.  If \spadvar{n} is not a valid index for a factor
      ++ (for example, less than 1 or too big), 1 is returned.  If
      ++ \spadvar{u} consists only of a unit, the unit is returned.

    nthFlag:    (%,Integer) -> fUnion
      ++ nthFlag(u,n) returns the information flag of the nth factor of
      ++ \spadvar{u}.  If \spadvar{n} is not a valid index for a factor
      ++ (for example, less than 1 or too big), "nil" is returned.

    numberOfFactors : %  -> NonNegativeInteger
      ++ numberOfFactors(u) returns the number of factors in \spadvar{u}.

    primeFactor:   (R,Integer) -> %
      ++ primeFactor(base,exponent) creates a factored object with
      ++ a single factor whose base is asserted to be prime
      ++ (flag = "prime").

    sqfrFactor:   (R,Integer) -> %
      ++ sqfrFactor(base,exponent) creates a factored object with
      ++ a single factor whose base is asserted to be square-free
      ++ (flag = "sqfr").

    flagFactor: (R,Integer, fUnion) -> %
      ++ flagFactor(base,exponent,flag) creates a factored object with
      ++ a single factor whose base is asserted to be properly
      ++ described by the information flag.

    unit:    % -> R
      ++ unit(u) extracts the unit part of the factorization.

    unitNormalize: % -> %
      ++ unitNormalize(u) normalizes the unit part of the factorization.
      ++ For example, when working with factored integers, this operation will
      ++ ensure that the bases are all positive integers.

    map:     (R -> R, %) -> %
      ++ map(fn,u) maps the function \userfun{fn} across the factors of
      ++ \spadvar{u} and creates a new factored object. Note: this clears
      ++ the information flags (sets them to "nil") because the effect of
      ++ \userfun{fn} is clearly not known in general.

    -- the following operations are conditional on R

    if R has GcdDomain then GcdDomain
    if R has RealConstant then RealConstant
--    if R has UniqueFactorizationDomain then UniqueFactorizationDomain

    if R has ConvertibleTo InputForm then ConvertibleTo InputForm

    if R has IntegerNumberSystem0 then
      rational?    : % -> Boolean
        ++ rational?(u) tests if \spadvar{u} is actually a
        ++ rational number (see \spadtype{Fraction Integer}).
      rational     : % -> Fraction Integer
        ++ rational(u) assumes spadvar{u} is actually a rational number
        ++ and does the conversion to rational number
        ++ (see \spadtype{Fraction Integer}).
      rationalIfCan: % -> Partial(Fraction Integer)
        ++ rationalIfCan(u) returns a rational number if u
        ++ really is one, and "failed" otherwise.

    if R has Eltable(R, R) then Eltable(%, %)
--    if R has Evalable(R) then Evalable(%)
    if R has InnerEvalable(Symbol, R) then InnerEvalable(Symbol, %)

  Implementation ==> add

  -- Representation:
    -- Note: exponents are allowed to be integers so that some special cases
    -- may be used in simplifications
    Rep == Record(unt:R, fct:List FF)
    import from Rep
    import from R
    default r: R
    default i: Integer

    import from BooleanFoldingOperations
    import from UniversalSegment Integer
    import from NonNegativeInteger
    import from List FF
    import from FF
    import from fUnion
    import from Fold R
    import from List R
    import from Partial R

    local apply(u: %, zz: 'unt'): R == rep(u).unt
    local apply(u: %, zz: 'fct'): List FF == rep(u).fct
    local [a: R, fct: List FF]: % == per [a, fct]

    if R has ConvertibleTo InputForm then
      convert(x:%):InputForm == never
#if 0
        empty?(lf := reverse factorList x) => convert(unit x)@InputForm
        l := empty()$List(InputForm)
        for rec in lf repeat
          ((rec.fctr) = 1) => messagePrint("WARNING (convert$Factored):_
 1 should not appear as factor.")$OutputForm
          iFactor : InputForm := binary( convert("::" :: Symbol)@InputForm, [convert(rec.fctr)@InputForm, (devaluate R)$Lisp :: InputForm ]$List(InputForm) )
          iExpon  : InputForm := convert(rec.xpnt)@InputForm
          iFun    : List InputForm :=
            rec.flg case nil =>
               [convert(#"nilFactor")@InputForm, iFactor, iExpon]$List(InputForm)
            rec.flg case sqfr =>
               [convert(#"sqfrFactor")@InputForm, iFactor, iExpon]$List(InputForm)
            rec.flg case prime =>
               [convert(#"primeFactor")@InputForm, iFactor, iExpon
                     ]$List(InputForm)
            rec.flg case irred =>
               [convert(#"irreducibleFactor")@InputForm, iFactor, iExpon
                     ]$List(InputForm)
            nil$List(InputForm)
          l := concat( iFun pretend InputForm, l )
--        one?(rec.xpnt) =>
--          l := concat(convert(rec.fctr)@InputForm, l)
--        l := concat(convert(rec.fctr)@InputForm ^ rec.xpnt, l)
        empty? l => convert(unit x)@InputForm
        if unit x ~= 1 then l := concat(convert(unit x)@InputForm,l)
        empty? rest l => first l
        binary(convert(_*::Symbol)@InputForm, l)@InputForm
#endif

    orderedR? := R has OrderedSet
    comparableR? := R has Comparable

  -- Private function signatures:
--    reciprocal              : % -> %
--    qexpand                 : % -> R
--    negexp?                 : % -> Boolean
--    SimplifyFactorization   : List FF -> List FF
--    LispLessP               : (FF, FF) -> Boolean
--    mkFF                    : (R, List FF) -> %
--    SimplifyFactorization1  : (FF, List FF) -> List FF
--    stricterFlag            : (fUnion, fUnion) -> fUnion

    nilFactor(r, i): %      == flagFactor(r, i, nil)
    sqfrFactor(r, i): %     == flagFactor(r, i, sqfr)
    irreducibleFactor(r, i): %      == flagFactor(r, i, irred)
    primeFactor(r, i): %    == flagFactor(r, i, prime)
    unit?(u: %): Boolean        == (empty? u.fct) and (not zero? u.unt)
    numberOfFactors(u: %): NonNegativeInteger == # u.fct
    0: %                    == [1, [[nil, 0, 1]$FF]]
    zero?(u: %): Boolean              == # u.fct = 1 and
                             (first u.fct).flg = nil and
                              zero?((first u.fct).fctr) and
--                               one? u.unt
                               (u.unt = 1)
    1: %                 == [1, empty()]
    one?(u: %): Boolean      == empty? u.fct and u.unt = 1
    mkFF(r, x: List FF): %   == [r, x]
    coerce(j:Integer):%  == (j::R)::%
    characteristic(): NonNegativeInteger == characteristic()$R
    (i:Integer) * (u:%): % == (i :: %) * u
    (r:R) * (u:%): %       == (r :: %) * u
    (u:%) * (r: R): %       == u * (r::%)
    expand(u: %): R             == retract u

    import from List Boolean;
    negexp?(x: %): Boolean   == _or/[negative?(y.xpnt) for y in factorList x]

    makeFR(u: R, l: List FF): % ==
-- normalizing code to be installed when contents are handled better
-- current squareFree returns the content as a unit part.
--        if (not unit?(u)) then
--            l := cons(["nil", u, 1]$FF,l)
--            u := 1
        unitNormalize mkFF(u, SimplifyFactorization l)

    if R has IntegerNumberSystem0 then
      rational?(x: %): Boolean     == true
      rationalIfCan(x: %): Partial Fraction Integer == [rational x]

      import from List Fraction Integer

      rational(x: %): Fraction Integer ==
        import from Fold Fraction Integer
        convert(unit x)@Integer *
           ((*)/[(convert(f.fctr)@Integer)::Fraction(Integer)
                                   ^ f.xpnt for f in factorList x])

    if R has Eltable(R, R) then
      elt(x:%, v:%): % == x(expand v)

    if R has Evalable(R) then
      eval(x:%, l:List Equation %): % == never --FIXME
--        import from Equation %
--        eval(x,[expand lhs e = expand rhs e for e in l]$List(Equation R))

--    if R has InnerEvalable(Symbol, R) then
      eval(x:%, ls:List Symbol, lv:List %): % ==
        eval(x, ls, [expand v for v in lv]$List(R))

    if R has RealConstant then
  --! negcount and rest commented out since RealConstant doesn't support
  --! positive? or negative?
  --  negcount: % -> Integer
  --  positive?(x:%):Boolean == not(zero? x) and even?(negcount x)
  --  negative?(x:%):Boolean == not(zero? x) and odd?(negcount x)
  --  negcount x ==
  --    n := count(s +-> negative?(s.fctr), factorList x)$List(FF)
  --    negative? unit x => n + 1
  --    n

      convert(x:%):Float ==
        import from List Float
        import from Float
	import from Fold Float
        convert(unit x)@Float *
                ((*)/[convert(f.fctr)@Float ^ f.xpnt for f in factorList x])

      convert(x:%):DoubleFloat ==
        import from List DoubleFloat
        import from DoubleFloat
	import from Fold DoubleFloat
        convert(unit x)@DoubleFloat *
          ((*)/[convert(f.fctr)@DoubleFloat ^ f.xpnt for f in factorList x])

    (u:%) * (v:%): % ==
      zero? u or zero? v => 0
--      one? u => v
      (u = 1) => v
--      one? v => u
      (v = 1) => u
      mkFF(unit u * unit v,
          SimplifyFactorization concat(factorList u, copy factorList v))

    (u:%) ^ (n: NonNegativeInteger): % ==
      mkFF(unit(u)^n, [[x.flg, x.fctr, n * x.xpnt] for x in factorList u])

    SimplifyFactorization(x: List FF): List FF ==
      empty? x => empty()
      x := sort!(LispLessP, x)
      x := SimplifyFactorization1(first x, rest x)
      if comparableR? then x := sort!(LispLessP, x)
      x

    SimplifyFactorization1(f: FF, x: List FF): List FF ==
      empty? x =>
        zero?(f.xpnt) => empty()
        cons(f, empty())
      f1 := first x
      f.fctr = f1.fctr =>
        SimplifyFactorization1([stricterFlag(f.flg, f1.flg),
                                      f.fctr, f.xpnt + f1.xpnt], rest x)
      l := SimplifyFactorization1(first x, rest x)
      zero?(f.xpnt) => l
      concat(f, l)


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

    retract(u:%):R ==
      negexp? u =>  error "Negative exponent in factored object"
      qexpand u

    qexpand(u: %): R ==
      import from Fold R
      unit u *
         ((*)/[y.fctr ^ (y.xpnt::NonNegativeInteger) for y in factorList u])

    retractIfCan(u:%):Partial(R) ==
      negexp? u => [failed]
      [qexpand u]

    LispLessP(y: FF, y1: FF): Boolean ==
      orderedR? and R has IntegerNumberSystem0 => y.fctr < y1.fctr
      comparableR? and R has OrderedSet => smaller?(y.fctr, y1.fctr)
      GGREATERP(y.fctr, y1.fctr) => false
      true

    import 
       GGREATERP: (R, R) -> Boolean
    from Foreign Lisp;

    stricterFlag(fl1: fUnion, fl2: fUnion): fUnion ==
      fl1 = prime   => fl1
      fl1 = irred   =>
        fl2 = prime => fl2
        fl1
      fl1 = sqfr    =>
        fl2 = nil   => fl1
        fl2
      fl2

--    if R has UniqueFactorizationDomain then
--      factor(a: %): Factored(%) == never
--      squareFree(a: %): Factored(%) == never

    if R has IntegerNumberSystem0
      then
        coerce(r:R):% ==
          factor(r)$IntegerFactorizationPackage(R) pretend %
      else
        if R has UniqueFactorizationDomain
          then
            coerce(r:R):% ==
              zero? r => 0
              unit? r => mkFF(r, empty())
              R has Field0 => error "zero divisor in a field"
              unitNormalize(squareFree(r) pretend %)
          else
            coerce(r:R):% ==
--              one? r => 1
              (r = 1) => 1
              unitNormalize mkFF(1, [[nil, r, 1]$FF])

    (u: %) = (v: %): Boolean ==
      (unit u = unit v) and # u.fct = # v.fct and
        set(factors u)$SRFE =$SRFE set(factors v)$SRFE

    -(u: %): % ==
      zero? u => u
      mkFF(- unit u, factorList u)

    recip(u: %): Partial %  ==
      not empty? factorList u => [failed]
      (pr := recip unit u) case failed => [failed]
      [mkFF(pr::R, empty())]

    reciprocal(u: %): % ==
      mkFF((recip unit u)::R,
                    [[y.flg, y.fctr, - y.xpnt]$FF for y in factorList u])

    exponent(u: %): Integer ==  -- exponent of first factor
      empty?(fl := factorList u) or zero? u => 0
      first(fl).xpnt

    nthExponent(u: %, i): Integer ==
      l := factorList u
      zero? u or i < 1 or i > #l::Integer => 0
      (l.(minIndex(l) + i - 1)).xpnt

    nthFactor(u: %, i): R ==
      zero? u => 0
      zero? i => unit u
      l := factorList u
      negative? i or i > #l::Integer => 1
      (l.(minIndex(l) + i - 1)).fctr

    nthFlag(u: %, i): fUnion ==
      l := factorList u
      zero? u or i < 1 or i > #l::Integer => nil
      (l.(minIndex(l) + i - 1)).flg

    flagFactor(r: R, i: Integer, fl: fUnion): % ==
      zero? i => 1
      zero? r => 0
      unitNormalize mkFF(1, [[fl, r, i]$FF])

    differentiate(u:%, deriv: R -> R): % ==
      import from List %
      import from Fold %
      import from Partial %
      ans := deriv(unit u) * ((u exquo unit(u)::%)::%)
      ans + ((+)/[fact.xpnt * deriv(fact.fctr) *
       ((u exquo (nilFactor(fact.fctr, 1)))::%) for fact in factorList u])

    map(fn: R -> R, u: %): % ==
     import from List %
     import from Fold %
     fn(unit u) * (_*/[irreducibleFactor(fn(f.fctr),f.xpnt) for f in factorList u])

    (u: %) exquo (v: %): Partial % ==
      import from Record(unit:R,canonical:R,associate:R)
      import from Record(unit:%,canonical:%,associate:%)
      empty?(x1 := factorList v) =>  [unitNormal(retract v).associate *  u]
      empty? factorList u => [failed]
      v1 := u * reciprocal v
      goodQuotient:Boolean := true
      while (goodQuotient and (not empty? x1)) repeat
        if x1.first.xpnt < 0
          then goodQuotient := false
          else x1 := rest x1
      goodQuotient => [v1]
      [failed]

    unitNormal(u: %): Record(unit:%,canonical:%,associate:%) == -- does a bunch of work, but more canonical
      import from Record(unit:R,canonical:R,associate:R)
      (ur := recip(un := unit u)) case failed => [1, u, 1]
      as := ur::R
      vl := empty()$List(FF)
      for x in factorList u repeat
        ucar := unitNormal(x.fctr)
        e := abs(x.xpnt)::NonNegativeInteger
        if x.xpnt < 0
          then  --  associate is recip of unit
            un := un * (ucar.associate ^ e)
            as := as * (ucar.unit ^ e)
          else
            un := un * (ucar.unit ^ e)
            as := as * (ucar.associate ^ e)
--        if not one?(ucar.canonical) then
        if not ((ucar.canonical) = 1) then
          vl := concat([x.flg, ucar.canonical, x.xpnt], vl)
      [mkFF(un, empty()), mkFF(1, reverse! vl), mkFF(as, empty())]

    unitNormalize(u: %): % ==
      import from Record(unit:%,canonical:%,associate:%)
      uca := unitNormal u
      mkFF(unit(uca.unit)*unit(uca.canonical),factorList(uca.canonical))


    copy(a: FF): FF == [a.flg, a.fctr, a.xpnt]

    if R has GcdDomain then
      (u: %) + (v: %): % ==
        zero? u => v
        zero? v => u
        v1 := reciprocal(u1 := gcd(u, v))
        (expand(u * v1) + expand(v * v1)) * u1

      gcd(u: %, v: %): % ==
        import from List List Integer
        import from List Integer
--        one? u or one? v => 1
        (u = 1) or (v = 1) => 1
        zero? u => v
        zero? v => u
        f1 := empty()$List(Integer)  -- list of used factor indices in x
        f2 := f1      -- list of indices corresponding to a given factor
        f3 := empty()$List(List Integer)    -- list of f2-like lists
        x := concat(factorList u, factorList v)
        for i in minIndex x .. maxIndex x repeat
          if not member?(i, f1) then
            f1 := concat(i, f1)
            f2 := [i]
            for j in i+1..maxIndex x repeat
              if x.i.fctr = x.j.fctr then
                  f1 := concat(j, f1)
                  f2 := concat(j, f2)
            f3 := concat(f2, f3)
        x1 := empty()$List(FF)
        while not empty? f3 repeat
          f1 := first f3
          if #f1 > 1 then
            i  := first f1
            y  := copy x.i
            f1 := rest f1
            while not empty? f1 repeat
              i := first f1
              if x.i.xpnt < y.xpnt then y.xpnt := x.i.xpnt
              f1 := rest f1
            x1 := concat(y, x1)
          f3 := rest f3
        if comparableR? then x1 := sort!(LispLessP, x1)
        mkFF(1, x1)

    else   -- R not a GCD domain
      (u: %) + (v: %): % ==
        zero? u => v
        zero? v => u
        irreducibleFactor(expand u + expand v, 1)

    if R has UniqueFactorizationDomain then
      prime?(u: %): Boolean ==
        not(empty?(l := factorList u)) and (empty? rest l) and
--                       one?(l.first.xpnt) and (l.first.flg = prime)
                       ((l.first.xpnt) = 1) and (l.first.flg = prime)
