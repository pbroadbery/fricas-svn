--DEPS:  lang SetCategory PositiveInteger_Base SetCategory Integer
#include "axiom"

import from Boolean;

RepeatedDoubling(S: SetCategory with { +: (%, %) -> %}):Exports ==Implementation where {
   Exports ==> with {
     double: (PositiveInteger,S) -> S;
       ++ double(i, r) multiplies r by i using repeated doubling.
       }
   Implementation ==> add {
     double(n: PositiveInteger, x: S): S == {
	import from Integer;
        one? n => x;
        odd?(n) =>
           x + double(shift(n,-1) pretend PositiveInteger,(x+x));
        double(shift(n,-1) pretend PositiveInteger,(x+x))
}}
}