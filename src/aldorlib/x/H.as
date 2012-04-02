--DEPS: Aggregate CoercibleTo OutputForm List_StreamAggregate
--DEPS: SetCategory shallowlyMutable Evalable Boolean Fold
#include "axiom.as"

import from Boolean;
#pile

H(S:Type): Category == with {
   map     : (S->S,%) -> %;
   if S has SetCategory then
      if S has Evalable S then Evalable S;
   default {
     if S has SetCategory then {
     if S has Evalable S then {
       import from List S;
       eval(u : %, l : List Equation S) : % == map((x: S): S +-> eval(x, l), u);
}}}}
