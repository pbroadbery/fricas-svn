--DEPS: Partial System String
#include "axiom.as"

import from System;
import from String;
import from Boolean;

RetractableTo(S: Type): Category == with {
    coerce:       S -> %;
      ++ coerce(a) transforms a into an element of %.
    retractIfCan: % -> Partial S;
      ++ retractIfCan(a) transforms a into an element of S if possible.
      ++ Returns "failed" if a cannot be made into an element of S.
    retract:      % -> S;
      ++ retract(a) transforms a into an element of S if possible.
      ++ Error: if a cannot be made into an element of S.
default {
    import from Partial S;
    retract(s: %): S == {
      failed?(u:=retractIfCan s) => error "not retractable";
      u::S}

}
}
