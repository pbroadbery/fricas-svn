--DEPS:  Integer NonNegativeInteger System String
#include "axiom"

import from System;
import from String;
import from Boolean;

extend PositiveInteger: with {
    1: %;
    one?: % -> Boolean;
    shift: (%, Integer) -> %;
    -: (%, %) -> Integer;
    odd?: % -> Boolean;
    coerce: % -> Integer;
    coerce: % -> NonNegativeInteger;
    coerce: NonNegativeInteger -> %;

    +: (%, %) -> %;
    random: % -> %;
} == Integer add {
    import from NonNegativeInteger;
    Rep ==> Integer;
    (a: %) - (b: %): Integer == rep(a) - rep(b);
    (a: %) + (b: %): Integer == rep(a) + rep(b);

    coerce(n: %): NonNegativeInteger == n pretend NonNegativeInteger;
    coerce(n: NonNegativeInteger): % == { zero? n => error "oops"; per(n::Integer)}
    coerce(n: %): Integer == rep n;
    coerce(n: Integer): % == { zero? n => error "oops"; per(n)}

    random(a: %): % == never
}
