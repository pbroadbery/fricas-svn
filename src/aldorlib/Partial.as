#include "axiom"
import from Boolean;

Partial(T: BasicType): BasicType with {
    success: T -> %;
    failed: () -> %;
    failed?: % -> Boolean;
    success?: % -> Boolean;
    value: % -> T;
} == add {
  Rep ==> Union(success: T, failed: 'failed');
  import from Rep;

  success(t: T): % == per [t];
  failed(): % == per [failed];
  success?(x: %): Boolean == rep(x) case success;
  failed?(x: %): Boolean == rep(x) case failed;
  value(x: %): T == rep(x).success;
  (a: %) = (b: %): Boolean == {
       rep(a) case failed => rep(b) case failed;
       rep(b) case success and rep(a).success = rep(b).success
  }
}
