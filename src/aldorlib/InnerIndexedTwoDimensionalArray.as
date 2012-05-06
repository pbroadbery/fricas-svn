--DEPS: TwoDimensionalArrayCategory PrimitiveArray
#include "axiom.as"

#pile

import from Boolean
import from System
import from String

-- This is an internal type which provides an implementation of
-- 2-dimensional arrays as PrimitiveArray's of PrimitiveArray's.
InnerIndexedTwoDimensionalArray(R: Type, mnRow: Integer, mnCol: Integer, _
				Row: FiniteLinearAggregate R,Col: FiniteLinearAggregate R):
  TwoDimensionalArrayCategory(R,Row,Col) with == 
 add

    Rep == PrimitiveArray PrimitiveArray R
    import from Rep
    import from PrimitiveArray R
    import from UniversalSegment Integer
    default m: %
    default rows, cols: NonNegativeInteger
    default a, r: R
    default i, j: Integer
--% Predicates

    empty? m: Boolean == empty?(rep m)$Rep

--% Primitive array creation

    empty(): % == per(empty()$Rep)

    new(rows,cols,a): % ==
      rows = 0 =>
        error "new: arrays with zero rows are not supported"
--      cols = 0 =>
--        error "new: arrays with zero columns are not supported"
      arr : PrimitiveArray PrimitiveArray R := new(rows,empty())
      for i in minIndex(arr)..maxIndex(arr) repeat
        qsetelt!(arr,i,new(cols,a))
      per arr
    
    new(rows, cols): % == 
      rows = 0 =>
        error "new: arrays with zero rows are not supported"
--      cols = 0 =>
--        error "new: arrays with zero columns are not supported"
      arr : PrimitiveArray PrimitiveArray R := new(rows,empty())
      for i in minIndex(arr)..maxIndex(arr) repeat
        qsetelt!(arr,i,new(cols))
      per arr
--% Size inquiries

    minRowIndex m: Integer == mnRow
    minColIndex m: Integer == mnCol
    maxRowIndex m: Integer == (nrows m)::Integer + mnRow - 1
    maxColIndex m: Integer == (ncols m)::Integer + mnCol - 1

    nrows m: NonNegativeInteger == (# rep(m))$Rep

    ncols m: NonNegativeInteger ==
      empty? m => 0
      # ((rep m).(minIndex(rep(m))$Rep))

--% Part selection/assignment

    qelt(m,i,j): R ==
      qelt(qelt(rep m,i - minRowIndex m)$Rep,j - minColIndex m)

    elt(m:%,i:Integer,j:Integer): R ==
      i < minRowIndex(m) or i > maxRowIndex(m) =>
        error "elt: index out of range"
      j < minColIndex(m) or j > maxColIndex(m) =>
        error "elt: index out of range"
      qelt(m,i,j)

    qsetelt!(m,i,j,r): R ==
      setelt(qelt(rep m,i - minRowIndex m)$Rep,j - minColIndex m,r)

    setelt(m:%,i:Integer,j:Integer,r:R): R ==
      i < minRowIndex(m) or i > maxRowIndex(m) =>
        error "setelt: index out of range"
      j < minColIndex(m) or j > maxColIndex(m) =>
        error "setelt: index out of range"
      qsetelt!(m,i,j,r)

    if R has SetCategory then
        latex(m : %) : String == never
