#include "axiom"

Integer: with {
    zero?: % -> Boolean;
    one?: % -> Boolean;
    shift: (%, Integer) -> %;
    -: % -> %;
    1: %;
    0: %;
    -: (%, %) -> %;
    odd?: % -> Boolean;
    coerce: % -> NonNegativeInteger;
    coerce: % -> PositiveInteger;
    >: (%, %) -> Boolean;
    <: (%, %) -> Boolean;
    =: (%, %) -> Boolean;
    -: (%, %) -> %;
    +: (%, %) -> %;
} == add {
    one?(x: %): Boolean == never;
    zero?(x: %): Boolean == never;
    shift(x: %, n: %): % == never;
    -(n: %): % == never;
    (a: %) - (b: %): % == never;
    (a: %) + (b: %): % == never;
    1: % == never;
    0: % == never;
    odd?(x: %): Boolean == never;
    coerce(x: %): NonNegativeInteger == never;
    coerce(x: %): PositiveInteger == never;
    (a: %) > (b: %): Boolean == never;
    (a: %) < (b: %): Boolean == never;
    (a: %) = (b: %): Boolean == never;
}


