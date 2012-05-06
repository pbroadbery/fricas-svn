--DEPS: OrderedSet Symbol String Boolean OutputForm

#include "axiom"

import from String;
import from Boolean;

SingletonAsOrderedSet: OrderedSet with {
              create:() -> %;
              convert:% -> Symbol;
} ==  add {
   default a, b: %;
   Rep ==> Symbol;
   import from Rep;
   create(): % == per("?"::Symbol);
   a<b: Boolean == false; -- only one element
   a=b: Boolean == true;
   coerce(zz: Symbol): % == per zz;
   min(a,b): % == a;  -- only one element
   max(a,b): % == a;  -- only one element
   convert a: Symbol == coerce("?");
   coerce(a: %): OutputForm == outputForm(rep a);
}
