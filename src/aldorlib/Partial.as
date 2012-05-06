--DEPS:  BasicType Boolean System String
#include "axiom"

import from System;
import from String;
import from Boolean;

Partial(T: Type): with {
    success: T -> %;
    failed: () -> %;
    failed?: % -> Boolean;
    success?: % -> Boolean;
    value: % -> T;
    coerce: % -> T;
    if T has BasicType then BasicType;

    -- These are for axiom compatibility.
    case: (%, 'failed') -> Boolean;
    case: (%, with) -> Boolean;
    bracket: T -> %;
    bracket: 'failed' -> %;

    export from T;
    export from 'failed';
} == add {
  Rep ==> Union(success: T, failed: 'failed');
  import from Rep;

  success(t: T): % == per [t];
  failed(): % == per [failed];
  success?(x: %): Boolean == rep(x) case success;
  failed?(x: %): Boolean == rep(x) case failed;
  value(x: %): T == rep(x).success;
  coerce(x: %): T == rep(x).success;
  if T has BasicType then {
  (a: %) = (b: %): Boolean == {
       rep(a) case failed => rep(b) case failed;
       rep(b) case success and rep(a).success = rep(b).success
  }
  }

  (a: %) case (t: with): Boolean == success? a;
  (a: %) case (s: 'failed'): Boolean == failed? a;
  [t: T]: % == success(t);
  [f: 'failed']: % == failed();
}
