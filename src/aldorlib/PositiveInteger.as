#include "axiom"

extend PositiveInteger: with {
    1: %;
    one?: % -> Boolean;
    shift: (%, Integer) -> %;
    -: (%, %) -> Integer;
    odd?: % -> Boolean;
    coerce: % -> NonNegativeInteger;
} == Integer add {
    Rep ==> Integer;
    (a: %) - (b: %): Integer == rep(a) - rep(b);
    coerce(n: %): NonNegativeInteger == n pretend NonNegativeInteger;
}
