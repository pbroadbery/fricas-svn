--DEPS: lang
#include "axiom.as"

#pile

CombinatorialFunctionCategory: Category == with
    binomial   : (%, %) -> %
      ++ binomial(n,r) returns the \spad{(n,r)} binomial coefficient
      ++ (often denoted in the literature by \spad{C(n,r)}).
      ++ Note: \spad{C(n,r) = n!/(r!(n-r)!)} where \spad{n >= r >= 0}.
    factorial  : % -> %
      ++ factorial(n) computes the factorial of n
      ++ (denoted in the literature by \spad{n!})
      ++ Note: \spad{n! = n (n-1)! when n > 0}; also, \spad{0! = 1}.
    permutation: (%, %) -> %
      ++ permutation(n, m) returns the number of
      ++ permutations of n objects taken m at a time.
      ++ Note: \spad{permutation(n,m) = n!/(n-m)!}.
