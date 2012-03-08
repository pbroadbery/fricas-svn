--DEPS:  Integer System 
#include "axiom"

--import from System;
--import from String;

extend NonNegativeInteger: with {
    0: %;
    1: %;
    one?: % -> Boolean;
    shift: (%, Integer) -> %;
    -: (%, %) -> Integer; -- Yes, Integer is right
    +: (%, %) -> %;
    *: (%, %) -> %;
    odd?: % -> Boolean;
    coerce: % -> Integer;

    zero?: % -> Boolean;
    =: (%, %) -> Boolean;
    ~=: (%, %) -> Boolean;
    <: (%, %) -> Boolean;
    >: (%, %) -> Boolean;

    quo: (%, %) -> %;

    random: % -> %;
} == Integer add {
    Rep ==> Integer;
    import from Rep;
    (a: %) + (b: %): % == per(rep(a) + rep(b));
    (a: %) - (b: %): Integer == rep(a) - rep(b);
    coerce(n: %): Integer == rep n;
    (a: %) = (b: %): Boolean == rep(a) = rep(b);
    (a: %) ~= (b: %): Boolean == rep(a) ~= rep(b);
    (a: %) < (b: %): Boolean == rep(a) < rep(b);
    (a: %) > (b: %): Boolean == rep(a) > rep(b);
    (a: %) quo (b: %): Integer == rep(a) quo rep(b);

    random(a: %): % == never; 
}

