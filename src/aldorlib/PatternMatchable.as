--DEPS: SetCategory init_Pattern init_PatternMatchResult
#include "axiom.as"

#pile
PatternMatchable(S:SetCategory): Category == SetCategory with
  patternMatch: (%, Pattern S, PatternMatchResult(S, %)) ->
                                                PatternMatchResult(S, %)
    ++ patternMatch(expr, pat, res) matches the pattern pat to the
    ++ expression expr. res contains the variables of pat which
    ++ are already matched and their matches (necessary for recursion).
    ++ Initially, res is just the result of \spadfun{new}
    ++ which is an empty list of matches.
