--DEPS:  List Boolean
#include "axiom.as"

import from Boolean;

FoldingTransformationCategory(T: with): Category == with {
  /: (%, List T) -> T
}

Fold(T: with): FoldingTransformationCategory(T) with {
	 /: (f: (T,T) -> T, List T) -> T;
	 folder: ((T, T) -> T) -> %
} == add {
  Rep ==> (T, T) -> T;
  folder(f: (T, T) -> T): % == per f;
  (f: (T,T) -> T) / (l: List T): T == (per f)/l;

  (folder: %) / (l: List T): T == {
     empty? rest l => first l;
     rep(folder)(first l, folder/rest l);
  }

}

AbsorbingFoldingTransformation(T: BasicType): FoldingTransformationCategory(T) with {
   folder: ((T, T) -> T, T) -> %
}
== add {
   Rep ==> Cross((T, T) -> T, T);
   folder(f: (T, T) -> T, t: T): % == per((f, t)@Rep);

   (fold: %) / (l: List T): T == {
      (fn, absorb) := rep fold;
      empty? rest l => first l;
      local value := first l;
      for x in rest l repeat {
	  x = absorb => return absorb;
          value :=  fn(value, x);
      }
      value
   }
}

BooleanFoldingOperations: with {
    _and: AbsorbingFoldingTransformation(Boolean);
    _or: AbsorbingFoldingTransformation(Boolean);
    export from AbsorbingFoldingTransformation Boolean;
}
== add {
   _and: AbsorbingFoldingTransformation(Boolean) == folder((a: Boolean, b: Boolean): Boolean +-> a and b, false);
   _or: AbsorbingFoldingTransformation(Boolean) == folder((a: Boolean, b: Boolean): Boolean +-> a or b, true);
}

