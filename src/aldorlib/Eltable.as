--DEPS:  SetCategory shallowlyMutable
#include "axiom.as"

import from Boolean;
#pile

Eltable(S:SetCategory, Index:Type): Category == with
  elt : (%, S) -> Index
     ++ elt(u,i) (also written: u . i) returns the element of u indexed by i.
     ++ Error: if i is not an index of u.
  apply: (%, S) -> Index
  default
    apply(x: %, s: S): Index == elt(x, s)