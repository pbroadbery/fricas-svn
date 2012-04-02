--DEPS:  lang SetCategory PositiveInteger_Base SetCategory Integer
#include "axiom"

import from Boolean;

default S: SetCategory with {
        *:(%,%)->%
             ++ x*y returns the product of x and y
}

RepeatedSquaring(S): Exports == Implementation where {
   Exports ==> with {
     expt: (S,PositiveInteger) -> S;
       ++ expt(r, i) computes r^i  by repeated squaring
   }
   Implementation ==> add {
     expt(x: S, n: PositiveInteger): S == {
        import from Integer;
        one? n => x;
        odd?(n)=> x * expt(x*x,shift(n,-1) pretend PositiveInteger);
        expt(x*x,shift(n,-1) pretend PositiveInteger);
}
}
}
