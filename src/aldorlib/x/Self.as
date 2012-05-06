--DEPS: lang Boolean Integer  List
#include "axiom.as"

import from Boolean;
#pile

Foo: Category == with {
       bar: Integer -> %;
       new: () -> Integer;
       zz: () -> List %;
       default {
       	       bar(a: %): Integer == new()$%;
	       zz(): List % == empty()$List(%);
       }
}


Foo2: Category ==  with {
       bar: String -> %;
       new: () -> String;
       default {
       	       bar(a: %): String == new()
       }
}

#if 0
ZZ(F: Foo): with {
   f: () -> ();
}
== add {
   import from F;
   import from Integer;
   f(): () == bar(22)
}
#endif
