--DEPS: None
#include "axiom.as"
#pile
NoneFunctions1(S:Type): Exports == Implementation where
  Exports ==> with
    coerce: S -> None
      ++ coerce(x) changes \spad{x} into an object of type
      ++ \spadtype{None}.

  Implementation ==> add
    coerce(s:S):None == s pretend None
