--DEPS: init_Matrix TwoDimensionalArrayCategory Vector_FiniteLinearAggregate InnerIndexedTwoDimensionalArray
#include "axiom.as"

import from Boolean;
import from Integer;

extend Matrix(S: with {SemiRng;AbelianMonoid}): TwoDimensionalArrayCategory(S, Vector S, Vector S) with {
   matrix: List List S -> %;
}
== InnerIndexedTwoDimensionalArray(S, 1, 1, Vector S, Vector S) add {
   matrix(l: List List S): % == never;
}

