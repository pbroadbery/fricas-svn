--DEPS: sexpr/init_SExpression
#include "axiom.as"

SX ==> SExpression

OutLisp: with {
    EQUAL: (SX, SX) -> Boolean;
    EQ: (SX, SX) -> Boolean;
    PAIRP: (SX) -> SX;
    STRINGP: (SX, SX) -> SX;
    IDENTP: (SX, SX) -> SX;
    INTEGERP: (SX, SX) -> SX;
    FLOATP: (SX, SX) -> SX;
    CAR: (SX) -> SX;
    CDR: (SX) -> SX;
    CONS: (SX, SX) -> SX;
    LENGTH: (SX) -> SX;
} == add {

}

