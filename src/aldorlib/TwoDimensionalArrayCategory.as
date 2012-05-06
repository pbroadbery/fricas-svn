--DEPS: HomogeneousAggregate shallowlyMutable finiteAggregate
--DEPS: FiniteLinearAggregate UniversalSegment Integer_OrderedRing
--DEPS: NonNegativeInteger_OrderedAbelianMonoidSup

#include "axiom.as"

#pile
import from Boolean
import from System
import from String

-- TODO: Sort out prefix comments
 -- TwoDimensionalArrayCategory is a general array category which
 -- allows different representations and indexing schemes.
 -- Rows and columns may be extracted with rows returned as objects
 -- of type Row and columns returned as objects of type Col.
 -- The index of the 'first' row may be obtained by calling the
 -- function 'minRowIndex'.  The index of the 'first' column may
 -- be obtained by calling the function 'minColIndex'.  The index of
 -- the first element of a 'Row' is the same as the index of the
 -- first column in an array and vice versa.
TwoDimensionalArrayCategory(R: Type, Row: FiniteLinearAggregate R,
			    Col: FiniteLinearAggregate R): Category 
 == Join(HomogeneousAggregate(R), shallowlyMutable, finiteAggregate) 
  with

--% Array creation

    new: (NonNegativeInteger,NonNegativeInteger,R) -> %
      ++ new(m,n,r) is an m-by-n array all of whose entries are r
    new: (NonNegativeInteger,NonNegativeInteger) -> %
      ++ new(m,n,r) is an m-by-n array all of whose entries are undefined
    fill!: (%,R) -> %
      ++ fill!(m,r) fills m with r's

--% Size inquiries

    minRowIndex : % -> Integer
      ++ minRowIndex(m) returns the index of the 'first' row of the array m
    maxRowIndex : % -> Integer
      ++ maxRowIndex(m) returns the index of the 'last' row of the array m
    minColIndex : % -> Integer
      ++ minColIndex(m) returns the index of the 'first' column of the array m
    maxColIndex : % -> Integer
      ++ maxColIndex(m) returns the index of the 'last' column of the array m
    nrows : % -> NonNegativeInteger
      ++ nrows(m) returns the number of rows in the array m
    ncols : % -> NonNegativeInteger
      ++ ncols(m) returns the number of columns in the array m

--% Part extractions

    elt: (%,Integer,Integer) -> R
      ++ elt(m,i,j) returns the element in the ith row and jth
      ++ column of the array m
      ++ error check to determine if indices are in proper ranges
    qelt: (%,Integer,Integer) -> R
      ++ qelt(m,i,j) returns the element in the ith row and jth
      ++ column of the array m
      ++ NO error check to determine if indices are in proper ranges
    elt: (%,Integer,Integer,R) -> R
      ++ elt(m,i,j,r) returns the element in the ith row and jth
      ++ column of the array m, if m has an ith row and a jth column,
      ++ and returns r otherwise
    row: (%,Integer) -> Row
      ++ row(m,i) returns the ith row of m
      ++ error check to determine if index is in proper ranges
    column: (%,Integer) -> Col
      ++ column(m,j) returns the jth column of m
      ++ error check to determine if index is in proper ranges
    parts: % -> List R
      ++ parts(m) returns a list of the elements of m in row major order

--% Part assignments

    setelt: (%,Integer,Integer,R) -> R
      -- will become setelt!
      ++ setelt(m,i,j,r) sets the element in the ith row and jth
      ++ column of m to r
      ++ error check to determine if indices are in proper ranges
    qsetelt!: (%,Integer,Integer,R) -> R
      ++ qsetelt!(m,i,j,r) sets the element in the ith row and jth
      ++ column of m to r
      ++ NO error check to determine if indices are in proper ranges
    setRow!: (%,Integer,Row) -> %
      ++ setRow!(m,i,v) sets to ith row of m to v
    setColumn!: (%,Integer,Col) -> %
      ++ setColumn!(m,j,v) sets to jth column of m to v

--% Map and Zip

    map: (R -> R,%) -> %
      ++ map(f,a) returns \spad{b}, where \spad{b(i,j) = f(a(i,j))} for all \spad{i, j}
    map!: (R -> R,%) -> %
      ++ map!(f,a)  assign \spad{a(i,j)} to \spad{f(a(i,j))} for all \spad{i, j}
    map:((R,R) -> R,%,%) -> %
      ++ map(f,a,b) returns \spad{c}, where \spad{c(i,j) = f(a(i,j),b(i,j))}
      ++ for all \spad{i, j}
    map:((R,R) -> R,%,%,R) -> %
      ++ map(f,a,b,r) returns \spad{c}, where \spad{c(i,j) = f(a(i,j),b(i,j))} when both
      ++ \spad{a(i,j)} and \spad{b(i,j)} exist;
      ++ else \spad{c(i,j) = f(r, b(i,j))} when \spad{a(i,j)} does not exist;
      ++ else \spad{c(i,j) = f(a(i,j),r)} when \spad{b(i,j)} does not exist;
      ++ otherwise \spad{c(i,j) = f(r,r)}.

    default

--% Predicates
     default f: R -> Boolean
     default m, m1, m2: %
     default v: %
     default i, j, k: Integer
     default n: NonNegativeInteger
     default r: R

     import from NonNegativeInteger
     import from UniversalSegment Integer

     any?(f,m): Boolean ==
      for i in minRowIndex(m)..maxRowIndex(m) repeat
        for j in minColIndex(m)..maxColIndex(m) repeat
          f(qelt(m,i,j)) => return true
      false

     every?(f,m): Boolean ==
      for i in minRowIndex(m)..maxRowIndex(m) repeat
        for j in minColIndex(m)..maxColIndex(m) repeat
          not f(qelt(m,i,j)) => return false
      true

     size?(m,n): Boolean == nrows(m) * ncols(m) = n
     less?(m,n): Boolean == nrows(m) * ncols(m) < n
     more?(m,n): Boolean == nrows(m) * ncols(m) > n

--% Size inquiries

     #(m): NonNegativeInteger == nrows(m) * ncols(m)

--% Part extractions

     elt(m,i,j,r): R ==
      i < minRowIndex(m) or i > maxRowIndex(m) => r
      j < minColIndex(m) or j > maxColIndex(m) => r
      qelt(m,i,j)

     count(f:R -> Boolean,m:%): NonNegativeInteger ==
      num : NonNegativeInteger := 0
      for i in minRowIndex(m)..maxRowIndex(m) repeat
        for j in minColIndex(m)..maxColIndex(m) repeat
          if f(qelt(m,i,j)) then num := num + 1
      num

     parts m: List R ==
      entryList : List R := nil()
      for i in maxRowIndex(m)..minRowIndex(m) by -1 repeat
        for j in maxColIndex(m)..minColIndex(m) by -1 repeat
          entryList := concat(qelt(m,i,j),entryList)
      entryList

--% Creation

     copy m: % ==
      ans := new(nrows m,ncols m)
      for i in minRowIndex(m)..maxRowIndex(m) repeat
        for j in minColIndex(m)..maxColIndex(m) repeat
          qsetelt!(ans,i,j,qelt(m,i,j))
      ans

     fill!(m,r): % ==
      for i in minRowIndex(m)..maxRowIndex(m) repeat
        for j in minColIndex(m)..maxColIndex(m) repeat
          qsetelt!(m,i,j,r)
      m

     default mf: R -> R
     default mf2: (R, R) -> R

     map(mf,m): % ==
      ans := new(nrows m,ncols m)
      for i in minRowIndex(m)..maxRowIndex(m) repeat
        for j in minColIndex(m)..maxColIndex(m) repeat
          qsetelt!(ans,i,j,mf(qelt(m,i,j)))
      ans

     map!(mf,m): % ==
      for i in minRowIndex(m)..maxRowIndex(m) repeat
        for j in minColIndex(m)..maxColIndex(m) repeat
          qsetelt!(m,i,j,mf(qelt(m,i,j)))
      m

     map(mf2,m1,m2): % ==
      (nrows(m1) ~= nrows(m2)) or (ncols(m1) ~= ncols(m2)) =>
        error "map: arguments must have same dimensions"
      ans := new(nrows m1,ncols m1)
      for i in minRowIndex(m1)..maxRowIndex(m1) repeat
        for j in minColIndex(m1)..maxColIndex(m1) repeat
          qsetelt!(ans,i,j, mf2(qelt(m1,i,j), qelt(m2,i,j)))
      ans
     
     map(mf2,m1,m2,r): % ==
      maxRow := max(maxRowIndex m1,maxRowIndex m2)
      maxCol := max(maxColIndex m1,maxColIndex m2)
      ans := new(max(nrows m1,nrows m2),max(ncols m1,ncols m2))
      for i in minRowIndex(m1)..maxRow repeat
        for j in minColIndex(m1)..maxCol repeat
          qsetelt!(ans,i,j, mf2(elt(m1,i,j,r),elt(m2,i,j,r)))
      ans

     setRow!(m,i,theRow: Row): % ==
      i < minRowIndex(m) or i > maxRowIndex(m) =>
        error "setRow!: index out of range"
      for j in minColIndex(m)..maxColIndex(m) _
        for k in minIndex(theRow)..maxIndex(theRow) repeat
          qsetelt!(m,i,j,theRow.k)
      m

     setColumn!(m,j,theCol: Col): % ==
      j < minColIndex(m) or j > maxColIndex(m) =>
        error "setColumn!: index out of range"
      for i in minRowIndex(m)..maxRowIndex(m) _
        for k in minIndex(theCol)..maxIndex(theCol) repeat
          qsetelt!(m,i,j,theCol.k)
      m

     if R has BasicType then -- was just '='

      m1 = m2: Boolean ==
        eq?(m1,m2) => true
        (nrows(m1) ~= nrows(m2)) or (ncols(m1) ~= ncols(m2)) => false
        for i in minRowIndex(m1)..maxRowIndex(m1) repeat
          for j in minColIndex(m1)..maxColIndex(m1) repeat
            not (qelt(m1,i,j) = qelt(m2,i,j)) => return false
        true

      member?(r,m): Boolean ==
        for i in minRowIndex(m)..maxRowIndex(m) repeat
          for j in minColIndex(m)..maxColIndex(m) repeat
            qelt(m,i,j) = r => return true
        false

      count(rr : R, m : %): NonNegativeInteger == count((x: R): Boolean +-> x = rr, m)

     if Row has shallowlyMutable then

      row(m,i): Row ==
        i < minRowIndex(m) or i > maxRowIndex(m) =>
          error "row: index out of range"
        theRow : Row := new(ncols m)
        for j in minColIndex(m)..maxColIndex(m) _
          for k in minIndex(theRow)..maxIndex(theRow) repeat
            qsetelt!(theRow,k,qelt(m,i,j))
        theRow

     if Col has shallowlyMutable then

      column(m,j): Col ==
        j < minColIndex(m) or j > maxColIndex(m) =>
          error "column: index out of range"
        theCol : Col := new(nrows m)
        for i in minRowIndex(m)..maxRowIndex(m) _
          for k in minIndex(theCol)..maxIndex(theCol) repeat
            qsetelt!(theCol,k,qelt(m,i,j))
        theCol

     if R has CoercibleTo(OutputForm) then
      coerce(m:%): OutputForm ==
        import from List OutputForm
        local l : List List OutputForm
        l := [[qelt(m,i,j) :: OutputForm _
                  for j in minColIndex(m)..maxColIndex(m)] _
                  for i in minRowIndex(m)..maxRowIndex(m)]
        matrix l
