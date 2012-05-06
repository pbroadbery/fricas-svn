--DEPS: QuotientFieldCategory0 Fraction_QuotientFieldCategory0 PolynomialFactorizationExplicit
--DEPS: Patternable FullyPatternMatchable
#include "axiom.as"

#pile

QuotientFieldCategory(S: IntegralDomain): Category ==
  Join(QuotientFieldCategory1 S, Patternable S, FullyPatternMatchable S) with
    /     : (S, S) -> %
       ++ d1 / d2 returns the fraction d1 divided by d2.
    numer  : % -> S
       ++ numer(x) returns the numerator of the fraction x.
    denom  : % -> S
       ++ denom(x) returns the denominator of the fraction x.
    numerator : % -> %
       ++ numerator(x) is the numerator of the fraction x converted to %.
    denominator : % -> %
       ++ denominator(x) is the denominator of the fraction x converted to %.
  with
    if S has StepThrough then StepThrough
    if S has RetractableTo Integer then
             RetractableTo Integer
             RetractableTo Fraction Integer
    if S has OrderedSet then OrderedSet
    if S has Comparable then Comparable
    if S has OrderedIntegralDomain then OrderedIntegralDomain
    if S has RealConstant then RealConstant
    if S has ConvertibleTo InputForm then ConvertibleTo InputForm
    if S has CharacteristicZero then CharacteristicZero
    if S has CharacteristicNonZero then CharacteristicNonZero
    if S has RetractableTo Symbol then RetractableTo Symbol
    if S has EuclideanDomain then
      wholePart: % -> S
        ++ wholePart(x) returns the whole part of the fraction x
        ++ i.e. the truncated quotient of the numerator by the denominator.
      fractionPart: % -> %
        ++ fractionPart(x) returns the fractional part of x.
        ++ x = wholePart(x) + fractionPart(x)
-- FIXME: strange random distribution used (#227).
    if S has IntegerNumberSystem0 then
      random: () -> %
        ++ random() returns a random fraction.  This function is deprecated.
      ceiling : % -> S
        ++ ceiling(x) returns the smallest integral element above x.
      floor: % -> S
        ++ floor(x) returns the largest integral element below x.

    default
     numerator(x: %): S == numer(x)::%
     denominator(x: %): S == denom(x) ::%

     if S has StepThrough then
       init(): % == init()$S / 1$S

       nextItem(n: %): % ==
         m:= nextItem(numer(n))
         m case "failed" =>
           error "We seem to have a Fraction of a finite object"
         m / 1

     map(fn: S-> S, x: %): %                      == (fn numer x) / (fn denom x)

     reducedSystem(m:Matrix %):Matrix S ==
      nrm := nrows m
      ncm := ncols m
      ans : Matrix S := new(nrm, ncm, 0)$(Matrix S)
      for i in 1..nrm repeat
        d := commonDenominator(row(m, i))$CommonDenominator(S, %, Vector %)
        for j in 1..ncm repeat
          ell := qelt(m,i,j)
          qsetelt!(ans, i, j, ((d exquo denom(ell))::S)*numer(ell))
      ans

     characteristic(): NonNegativeInteger == characteristic()$S

     differentiate(x:%, deriv:S -> S): % ==
        n := numer x
        d := denom x
        (deriv n * d - n * deriv d) / (d^2)

     if S has ConvertibleTo InputForm then
      convert(x:%):InputForm == (convert numer x) / (convert denom x)

     if S has RealConstant then
      convert(x:%):Float == (convert numer x) / (convert denom x)
      convert(x:%):DoubleFloat == (convert numer x) / (convert denom x)

     if S has OrderedSet then
       (x:%) < (y:%): Boolean ==
         (numer x  * denom y) < (numer y * denom x)

     if S has Comparable then
       smaller?(x:%,  y:%): Boolean ==
         smaller?(numer x  * denom y, numer y * denom x)

     if (S has EuclideanDomain) then
      fractionPart(x: %): % == x - (wholePart(x)::%)

     if S has RetractableTo Symbol then
      coerce(s:Symbol): %  == s::S::%
      retract(x:%): Symbol == retract(retract(x)@S)

      retractIfCan(x:%): Partial(Symbol) ==
        (r := retractIfCan(x)@Partial(Symbol)) case failed =>[failed]
        retractIfCan(r::S)

     if (S has ConvertibleTo Pattern Integer) then
      convert(x:%):Pattern(Integer)==(convert numer x)/(convert denom x)

      if (S has PatternMatchable Integer) then
        patternMatch(x:%, p:Pattern Integer,
         l:PatternMatchResult(Integer, %)): PatternMatchResult(Integer, %) ==
           patternMatch(x, p,
                     l)$PatternMatchQuotientFieldCategory(Integer, S, %)

     if (S has ConvertibleTo Pattern Float) then
      convert(x:%):Pattern(Float) == (convert numer x)/(convert denom x)

      if (S has PatternMatchable Float) then
        patternMatch(x:%, p:Pattern Float,
         l:PatternMatchResult(Float, %)): PatternMatchResult(Float, %) ==
           patternMatch(x, p,
                       l)$PatternMatchQuotientFieldCategory(Float, S, %)

     if S has RetractableTo Integer then
        coerce(x:Fraction Integer):% == numer(x)::% / denom(x)::%

      --if not(S is Integer) then
      --  retract(x:%):Integer == retract(retract(x)@S)

      --  retractIfCan(x:%):Partial(Integer) ==
      --    (u := retractIfCan(x)) case "failed" =>
      --      "failed"
      --    retractIfCan(u::S)

-- FIXME: strange random distribution used (#227).
     if S has IntegerNumberSystem0 then
      random():% ==
        while zero?(d:=random()$S) repeat d
        random()$S / d

     reducedSystem(m:Matrix %, v:Vector %):
      Record(mat:Matrix S, vec:Vector S) ==
        n := reducedSystem(horizConcat(v::Matrix(%), m))@Matrix(S)
        [subMatrix(n, minRowIndex n, maxRowIndex n, 1 + minColIndex n,
                                maxColIndex n), column(n, minColIndex n)]

