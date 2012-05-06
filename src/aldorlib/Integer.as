--DEPS:  lang init_Boolean init_NonNegativeInteger init_PositiveInteger Basic Boolean 
#include "axiom"

Integer: with {
    integer: Literal -> %;
    zero?: % -> Boolean;
    one?: % -> Boolean;
    positive?: % -> Boolean;
    shift: (%, Integer) -> %;
    -: % -> %;
    1: %;
    0: %;
    -: (%, %) -> %;
    odd?: % -> Boolean;
    even?: % -> Boolean;
    coerce: % -> NonNegativeInteger;
    coerce: % -> PositiveInteger;
    >=: (%, %) -> Boolean;
    <=: (%, %) -> Boolean;
    >: (%, %) -> Boolean;
    <: (%, %) -> Boolean;
    =: (%, %) -> Boolean;
    ~=: (%, %) -> Boolean;
    -: (%, %) -> %;
    +: (%, %) -> %;
    *: (%, %) -> %;
    ^: (%, %) -> %;
    sample: %;
    quo: (%, %) -> %;
    rem: (%, %) -> %;
    divide: (%, %) -> (%, %);
    positiveRemainder: (%, %) -> %;
    addmod: (%, %, %) -> %;
    submod: (%, %, %) -> %;
    mulmod: (%, %, %) -> %;
    powmod: (%, %, %) -> %;

    random: % -> %;
    integer: Literal -> %;

} == add {
    Rep ==> BasicInteger;
    import from Rep;
    import from BasicBoolean;
    import from BasicArray;

    one?(x: %): Boolean == (rep(x) = one()$Rep)::Boolean;
    zero?(x: %): Boolean == (zero? rep x)::Boolean;
    positive?(x: %): Boolean == positive?(rep x)::Boolean;
    negative?(x: %): Boolean == negative?(rep x)::Boolean;
    even?(x: %): Boolean == even?(rep x)::Boolean;
    odd?(x: %): Boolean == odd?(rep x)::Boolean;

    shift(x: %, n: %): % == never;
    -(n: %): % == per negate rep n;
    (a: %) - (b: %): % == per(rep a - rep b);
    (a: %) + (b: %): % == per(rep a + rep b);
    (a: %) * (b: %): % == per(rep a * rep b);

    1: % == per one();
    0: % == per zero();

    coerce(x: %): NonNegativeInteger == { x < 0 => never; x pretend NonNegativeInteger};
    coerce(x: %): PositiveInteger == { x <= 0 => never; x pretend PositiveInteger};
    (a: %) >  (b: %): Boolean == (rep a >  rep b)::Boolean;
    (a: %) <  (b: %): Boolean == (rep a <  rep b)::Boolean;
    (a: %) >= (b: %): Boolean == (rep a >= rep b)::Boolean;
    (a: %) <= (b: %): Boolean == (rep a <= rep b)::Boolean;
    (a: %) =  (b: %): Boolean == (rep a =  rep b)::Boolean;
    (a: %) ~= (b: %): Boolean == (rep a ~= rep b)::Boolean;
    (a: %) quo (b: %): % == per (rep a quo rep b);
    (a: %) mod (b: %): % == per (rep a mod rep b);
    (a: %) rem (b: %): % == per (rep a rem rep b);
    (a: %) ^ (b: %): %   == per (rep a ^ rep b);
    
    divide(a: %, b: %): (%, %) == { (q, r) := divide(rep a, rep b); (per q, per r)}
    positiveRemainder(a: %, b: %): % == a rem b;
    import from Literal;
    integer(l: Literal): % == per convert(l::BasicArray);
    sample: % == 0;
    addmod(x: %, y: %, p: %): % == (x + y) mod p;
    submod(x: %, y: %, p: %): % == (x - y) mod p;
    mulmod(x: %, y: %, p: %): % == (x * y) mod p;
    powmod(x: %, y: %, p: %): % == per powmod(rep x, rep y, rep p);

    random(x: %): % == never;

}


