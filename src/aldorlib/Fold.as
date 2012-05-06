--DEPS:  List
#include "axiom.as"

import from Boolean;

Fold(T: with): with {
	 /: (f: (T,T) -> T, List T) -> T;
} == add {
  (f: (T,T) -> T) / (l: List T): T == {
     empty? rest l => first l;
     f(first l, f/rest l);
  }

}
