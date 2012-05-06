--DEPS:  BasicType Boolean
#include "axiom"
import from Boolean;

Partial(T: Type): with {
    success: T -> %;
    failed: () -> %;
    failed?: % -> Boolean;
    success?: % -> Boolean;
    value: % -> T;
    coerce: % -> T;
    if T has BasicType then BasicType;
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
}
