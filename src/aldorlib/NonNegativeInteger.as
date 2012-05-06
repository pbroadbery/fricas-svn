#include "axiom"

extend NonNegativeInteger: with {
    0: %;
    1: %;
    one?: % -> Boolean;
    shift: (%, Integer) -> %;
    -: (%, %) -> Integer;
    +: (%, %) -> %;
    odd?: % -> Boolean;
    coerce: % -> Integer;
    zero?: % -> Boolean;
    =: (%, %) -> Boolean;
    <: (%, %) -> Boolean;
    >: (%, %) -> Boolean;
} == Integer add {
    Rep ==> Integer;
    import from Rep;
    (a: %) + (b: %): % == per(rep(a) + rep(b));
    (a: %) - (b: %): Integer == rep(a) - rep(b);
    coerce(n: %): Integer == rep n;
    (a: %) = (b: %): Boolean == rep(a) = rep(b);
    (a: %) < (b: %): Boolean == rep(a) < rep(b);
    (a: %) > (b: %): Boolean == rep(a) > rep(b);
 
}

