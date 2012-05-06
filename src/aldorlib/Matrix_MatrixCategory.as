--DEPS: Matrix_TwoDimensionalArrayCategory MatrixCategory
#include "axiom.as"

import from Boolean;
import from Integer;

extend Matrix(S: with {SemiRng;AbelianMonoid}): MatrixCategory(S, Vector S, Vector S) with {
}
== InnerIndexedTwoDimensionalArray(S, 1, 1, Vector S, Vector S) add {
}

