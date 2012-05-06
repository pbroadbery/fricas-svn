--DEPS: Module CommutativeRing OrderedAbelianGroup OutputForm
--DEPS: System String

#include "axiom.as"

import from System;
import from String;
import from Boolean;

Localize(M : Module R, R : CommutativeRing): Module R with {
      if M has OrderedAbelianGroup then OrderedAbelianGroup;
      _/ : (%, R) -> %;
         ++ x / d divides the element x by d.
      _/ : (M, R) -> %;
         ++ m / d divides the element m by d.
      numer: % -> M;
         ++ numer x returns the numerator of x.
      denom: % -> R;
         ++ denom x returns the denominator of x.
} == add {
    --representation
      Rep == Record(num : M, den : R);
      import from Rep;
    --declarations
      default x, y: %;
      default n: Integer;
      default m: M;
      default r: R;
      default d: R;
    --definitions
      0: % == per [0,1];
      zero? x: Boolean == zero? (rep(x).num);
      -x: %== per [-rep(x).num,rep(x).den];
      x=y: Boolean == rep(y).den*rep(x).num = rep(x).den*rep(y).num;
      numer x: M == rep(x).num;
      denom x: R == rep(x).den;
      if M has OrderedAbelianGroup then
        x < y: Boolean == {
--             if rep(y).den::R < 0 then (x,y):=(y,x);
--             if rep(x).den::R < 0 then (x,y):=(y,x);
             rep(y).den*rep(x).num < rep(x).den*rep(y).num}
--      x+y: % == [y.den*x.num+x.den*y.num, x.den*y.den];
      x+y: % == per [denom y*numer x + denom x*numer y, denom x*denom y];
      n*x: % == per [n*rep(x).num, rep(x).den];
      r*x: % == if r=rep(x).den then per [rep(x).num,1] else per [r*rep(x).num,rep(x).den];
      x*r: % == if r=rep(x).den then per [rep(x).num,1] else per [rep(x).num * r,rep(x).den];
      x/d: % == {
        zero?(u:R:=d*rep(x).den) => error "division by zero";
        per [rep(x).num,u]}
      m/d: % == if zero? d then error "division by zero" else per [m,d];
      coerce(x:%):OutputForm == {
--        one?(xd:=rep(x).den) => (rep(x).num)::OutputForm;
        ((xd:=rep(x).den) = 1) => (rep(x).num)::OutputForm;
        (rep(x).num)::OutputForm / (xd::OutputForm)}

      latex(x:%): String =={
--        one?(xd:=x.den) => latex(x.num);
        ((xd:=rep(x).den) = 1) => latex(rep(x).num);
        nl : String := concat("{", concat(latex(rep(x).num), "}")$String)$String;
        dl : String := concat("{", concat(latex(rep(x).den), "}")$String)$String;
        concat("{ ", concat(nl, concat(" \over ", concat(dl, " }")$String)$String)$String)$String}
}
