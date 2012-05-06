--DEPS: QuotientFieldCategory0
#include "axiom.as"
#pile

CommonDenominator(R: IntegralDomain, Q: QuotientFieldCategory0 R, A: FiniteLinearAggregate Q): Exports == Implementation where
  Exports ==> with
    commonDenominator: A -> R
      ++ commonDenominator([q1,...,qn]) returns a common denominator
      ++ d for q1,...,qn.
    clearDenominator : A -> A
      ++ clearDenominator([q1,...,qn]) returns \spad{[p1,...,pn]} such that
      ++ \spad{qi = pi/d} where d is a common denominator for the qi's.
    splitDenominator : A -> Record(num: A, den: R)
      ++ splitDenominator([q1,...,qn]) returns
      ++ \spad{[[p1,...,pn], d]} such that
      ++ \spad{qi = pi/d} and d is a common denominator for the qi's.

  Implementation ==> add
    default l: A
    default a, b: Q
    import from R

    clearDenominator l: A ==
      d := commonDenominator l
      map((x: Q): Q +-> numer(d*x)::Q, l)

    splitDenominator l: Record(num: A, den: R) ==
      d := commonDenominator l
      [map((x: Q): Q +-> numer(d*x)::Q, l), d]

    if R has GcdDomain then
      qlcm(a, b): Q       == lcm(numer a, numer b)::Q
      commonDenominator l: R == numer reduce(qlcm, map((x: Q): Q +-> denom(x)::Q, l), 1)
    else
      commonDenominator l: R == numer reduce(*, map((x: Q): Q +-> denom(x)::Q, l), 1)

