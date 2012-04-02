--DEPS:  SingleInteger init_Character init_Integer Boolean
#include "axiom.as"

LString: with {
    QENUM: (%, SingleInteger) -> Character;
    QESET: (%, SingleInteger, Character) -> ();
    NEW: (SingleInteger) -> %;
    string: Literal -> %;
    string: Integer -> %;
    string: SingleInteger -> %;
    length: % -> SingleInteger;

    =: (%, %) -> Boolean;
} 
== add {
    Rep ==> Ptr;
    import from Machine;

    import {
       MAKE_-STRING: SInt -> Ptr;
       LENGTH: Ptr -> SInt;
       EQUAL: (Ptr, Ptr) -> Boolean;
       BOOT_:_:SUBSTRING: (Arr, SInt, SInt) -> Arr;
    } from Foreign Lisp;

    import { strLength: Arr -> SInt } from Foreign;

    import { formatBInt: BInt -> Arr } from Foreign;
    import { formatSInt: SInt -> Arr } from Foreign;

    local SUBSTRING(a: Arr, n: SInt, l: SInt): Arr == BOOT_:_:SUBSTRING(a, n, l);

    local srep(n: SingleInteger): SInt == n pretend SInt;
    local sper(n: SInt): SingleInteger == n pretend SingleInteger;

    local crep(c: Character): Char == c pretend Char;
    local cper(c: Char): Character == c pretend Character;

    local arep(a: %): Arr == a pretend Arr;
    local aper(a: Arr): % == a pretend %;

    length(a: %): SingleInteger == sper LENGTH(rep a);
    QENUM(a: %, n: SingleInteger): Character == cper get(Char)(arep a, srep n);
    QESET(a: %, n: SingleInteger, c: Character): () == set!(Char)(arep(a), srep n, crep c);

    NEW(n: SingleInteger, c: Character): % == never;
    NEW(n: SingleInteger): % == per MAKE_-STRING(srep n);

    string(l: Literal): % == aper SUBSTRING(l pretend Arr, 0, strLength(l pretend Arr) - 1);
    
    string(x: SingleInteger): % == formatSInt(srep x) pretend %;
    string(x: Integer): % == formatBInt(x pretend BInt) pretend %;

    (a: %) = (b: %): Boolean == EQUAL(rep a, rep b);
}

