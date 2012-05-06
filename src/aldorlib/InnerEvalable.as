--DEPS:  SetCategory List
#include "axiom.as"

import from Boolean;

InnerEvalable(A:SetCategory, B:Type): Category == SetCategory with {
    eval: (%, A, B) -> %;
       ++ eval(f, x, v) replaces x by v in f.
    eval: (%, List A, List B) -> %;
       ++ eval(f, [x1,...,xn], [v1,...,vn]) replaces xi by vi in f.
 default {
    import from List A, List B;
    eval(f:%, x:A, v:B): % == eval(f, [x], [v]);
}
}