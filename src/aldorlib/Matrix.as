--DEPS: init_Matrix TwoDimensionalArrayCategory
#include "axiom.as"

#pile

extend Matrix(T: with {SemiRng;AbelianMonoid}): TwoDimensionalArrayCategory() with 
== InnerIndexedTwoDimensionalArray(R,mnRow,mnCol,Row,Col) add

