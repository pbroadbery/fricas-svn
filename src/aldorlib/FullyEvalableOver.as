--DEPS: Eltable Evalable List Equation_SetCategory Symbol_SetCategory
#include "axiom.as"
#pile

FullyEvalableOver(R:SetCategory): Category == with
    import from R
    map: (R -> R, %) -> %
        ++ map(f, ex) evaluates ex, applying f to values of type R in ex.
    if R has Eltable(R, R) then Eltable(R, %)
    if R has Evalable(R) then Evalable(R)
    if R has InnerEvalable(Symbol, R) then InnerEvalable(Symbol, R)
    default
     if R has Eltable(R, R) then
      elt(x : %, r : R): % == map((y: R): R +-> y(r), x)

     if R has Evalable(R) then
      eval(x : %, l : List Equation R): % == map((y: R): R +-> eval(y, l), x)

     if R has InnerEvalable(Symbol, R) then
      eval(x : %, ls : List Symbol, lv : List R): % ==
          map((y: R): R +-> eval(y, ls, lv), x)
