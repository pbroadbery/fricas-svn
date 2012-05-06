#include "axiom.as"

Fold(T: with, 0: T): with {
	 /: (f: (T,T) -> T, List T) -> T;
} == add {
  (f: (T,T) -> T) / (l: List T): T == {
     acc := 0;
     for i in l repeat acc := f(acc, i);
     acc;
  }

}
