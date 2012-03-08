--DEPS: init_NonNegativeInteger init_PositiveInteger  
--DEPS: Boolean init_String init_SingleInteger
#include "axiom"

TheInteger: Category == with;
Integer: TheInteger with {
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
    coerce: % -> SingleInteger;
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
    Rep ==> BInt;
    import from Machine;

    local coerce(b: Bool): Boolean == b pretend Boolean;

    one?(x: %): Boolean == (rep(x) = 1)::Boolean;
    zero?(x: %): Boolean == (zero? rep x)::Boolean;
    positive?(x: %): Boolean == positive?(rep x)::Boolean;
    negative?(x: %): Boolean == negative?(rep x)::Boolean;
    even?(x: %): Boolean == even?(rep x)::Boolean;
    odd?(x: %): Boolean == odd?(rep x)::Boolean;

    shift(x: %, n: %): % == never;
    -(n: %): % == per(-(rep n));
    (a: %) - (b: %): % == per(rep a - rep b);
    (a: %) + (b: %): % == per(rep a + rep b);
    (a: %) * (b: %): % == per(rep a * rep b);

    1: % == per 1;
    0: % == per 0;

    coerce(x: %): NonNegativeInteger == { x < 0 => never; x pretend NonNegativeInteger};
    coerce(x: %): PositiveInteger == { x <= 0 => never; x pretend PositiveInteger};
    coerce(x: %): SingleInteger == convert(rep x)@SInt pretend SingleInteger;

    (a: %) >  (b: %): Boolean == b < a;
    (a: %) <  (b: %): Boolean == (rep a <  rep b)::Boolean;
    (a: %) >= (b: %): Boolean == b <= a;
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
    integer(l: Literal): % == per convert(l pretend Arr);
    sample: % == 0;
    addmod(x: %, y: %, p: %): % == (x + y) mod p;
    submod(x: %, y: %, p: %): % == (x - y) mod p;
    mulmod(x: %, y: %, p: %): % == (x * y) mod p;
    powmod(x: %, y: %, p: %): % == per mod_^(rep x, rep y, rep p);

    random(x: %): % == never;
}


