--DEPS: IntegralDomain PatternMatchable 
#include "axiom.as"
#pile

#if 0
PatternMatchQuotientFieldCategory(S: SetCategory, R: Join(IntegralDomain, PatternMatchable S, ConvertibleTo Pattern S), Q: QuotientFieldCategory0 R):Exports == Implementation where

  PAT ==> Pattern S
  PRQ ==> PatternMatchResult(S, Q)

  Exports ==> with
    patternMatch: (Q, PAT, PRQ) -> PRQ
      ++ patternMatch(a/b, pat, res) matches the pattern pat to the
      ++ quotient a/b; res contains the variables of pat which
      ++ are already matched and their matches.

  Implementation ==> add
    import PatternMatchPushDown(S, R, Q)

    patternMatch(x, p, l) ==
      generic? p => addMatch(p, x, l)
      (r := retractIfCan x)@Union(R, "failed") case R =>
        patternMatch(r::R, p, l)
      (u := isQuotient p) case Record(num:PAT, den:PAT) =>
        ur := u::Record(num:PAT, den:PAT)
        failed?(l := patternMatch(numer x, ur.num, l)) => l
        patternMatch(denom x, ur.den, l)
      failed()

#endif
