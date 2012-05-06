#include "axiom.as"

Evalable(R:SetCategory): Category == InnerEvalable(R,R) with {
    eval: (%, Equation R) -> %;
       ++ eval(f,x = v) replaces x by v in f.
    eval: (%, List Equation R) -> %;
       ++ eval(f, [x1 = v1,...,xn = vn]) replaces xi by vi in f.
 default {
    import from R;
    import from List Equation R;
    import from Equation R;
    eval(f:%, eq:Equation R): % == eval(f, [eq]);
    eval(f:%, xs:List R,vs:List R): % == eval(f,[(x=v)@Equation R for x in xs for v in vs]);
}
}
