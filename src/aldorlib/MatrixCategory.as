--DEPS: AbelianMonoid FiniteLinearAggregate EuclideanDomain0 
--DEPS: TwoDimensionalArrayCategory Field0 

#include "axiom.as"

#pile
import from Boolean
import from System
import from String

NNI ==> NonNegativeInteger
MatrixCategory(R: Join(SemiRng, AbelianMonoid),Row: FiniteLinearAggregate R, Col: FiniteLinearAggregate R): Category 
 == Join(TwoDimensionalArrayCategory(R,Row,Col),shallowlyMutable, finiteAggregate) 
   with

--% Predicates

    square?  : % -> Boolean
      ++ \spad{square?(m)} returns true if m is a square matrix
      ++ (i.e. if m has the same number of rows as columns) and false otherwise.
    diagonal?: % -> Boolean
      ++ \spad{diagonal?(m)} returns true if the matrix m is square and
      ++ diagonal (i.e. all entries of m not on the diagonal are zero) and
      ++ false otherwise.
    symmetric?: % -> Boolean
      ++ \spad{symmetric?(m)} returns true if the matrix m is square and
      ++ symmetric (i.e. \spad{m[i,j] = m[j,i]} for all i and j) and false
      ++ otherwise.
    if R has AbelianGroup then
        antisymmetric? : % -> Boolean
          ++ \spad{antisymmetric?(m)} returns true if the matrix m is
          ++ square and antisymmetric (i.e. \spad{m[i, j] = -m[j, i]} for
          ++ all i and j) and false otherwise.

--% Creation

    zero: (NonNegativeInteger,NonNegativeInteger) -> %
      ++ \spad{zero(m,n)} returns an m-by-n zero matrix.
    matrix: List List R -> %
      ++ \spad{matrix(l)} converts the list of lists l to a matrix, where the
      ++ list of lists is viewed as a list of the rows of the matrix.
    scalarMatrix: (NonNegativeInteger,R) -> %
      ++ \spad{scalarMatrix(n,r)} returns an n-by-n matrix with r's on the
      ++ diagonal and zeroes elsewhere.
    diagonalMatrix: List R -> %
      ++ \spad{diagonalMatrix(l)} returns a diagonal matrix with the elements
      ++ of l on the diagonal.
    diagonalMatrix: List % -> %
      ++ \spad{diagonalMatrix([m1,...,mk])} creates a block diagonal matrix
      ++ M with block matrices {\em m1},...,{\em mk} down the diagonal,
      ++ with 0 block matrices elsewhere.
      ++ More precisly: if \spad{ri := nrows mi}, \spad{ci := ncols mi},
      ++ then m is an (r1+..+rk) by (c1+..+ck) - matrix  with entries
      ++ \spad{m.i.j = ml.(i-r1-..-r(l-1)).(j-n1-..-n(l-1))}, if
      ++ \spad{(r1+..+r(l-1)) < i <= r1+..+rl} and
      ++ \spad{(c1+..+c(l-1)) < i <= c1+..+cl},
      ++ \spad{m.i.j} = 0  otherwise.
    coerce: Col -> %
      ++ \spad{coerce(col)} converts the column col to a column matrix.
    transpose: Row -> %
      ++ \spad{transpose(r)} converts the row r to a row matrix.

--% Creation of new matrices from old

    transpose: % -> %
      ++ \spad{transpose(m)} returns the transpose of the matrix m.
    squareTop: % -> %
      ++ \spad{squareTop(m)} returns an n-by-n matrix consisting of the first
      ++ n rows of the m-by-n matrix m. Error: if
      ++ \spad{m < n}.
    horizConcat: (%,%) -> %
      ++ \spad{horizConcat(x,y)} horizontally concatenates two matrices with
      ++ an equal number of rows. The entries of y appear to the right
      ++ of the entries of x.  Error: if the matrices
      ++ do not have the same number of rows.
    vertConcat: (%,%) -> %
      ++ \spad{vertConcat(x,y)} vertically concatenates two matrices with an
      ++ equal number of columns. The entries of y appear below
      ++ of the entries of x.  Error: if the matrices
      ++ do not have the same number of columns.

--% Part extractions/assignments

    listOfLists: % -> List List R
      ++ \spad{listOfLists(m)} returns the rows of the matrix m as a list
      ++ of lists.
    elt: (%,List Integer,List Integer) -> %
      ++ \spad{elt(x,rowList,colList)} returns an m-by-n matrix consisting
      ++ of elements of x, where \spad{m = # rowList} and \spad{n = # colList}.
      ++ If \spad{rowList = [i<1>,i<2>,...,i<m>]} and \spad{colList =
      ++ [j<1>,j<2>,...,j<n>]}, then the \spad{(k,l)}th entry of
      ++ \spad{elt(x,rowList,colList)} is \spad{x(i<k>,j<l>)}.
    setelt: (%,List Integer,List Integer, %) -> %
      ++ \spad{setelt(x,rowList,colList,y)} destructively alters the matrix x.
      ++ If y is \spad{m}-by-\spad{n}, \spad{rowList = [i<1>,i<2>,...,i<m>]}
      ++ and \spad{colList = [j<1>,j<2>,...,j<n>]}, then \spad{x(i<k>,j<l>)}
      ++ is set to \spad{y(k,l)} for \spad{k = 1,...,m} and \spad{l = 1,...,n}.
    swapRows!: (%,Integer,Integer) -> %
      ++ \spad{swapRows!(m,i,j)} interchanges the \spad{i}th and \spad{j}th
      ++ rows of m. This destructively alters the matrix.
    swapColumns!: (%,Integer,Integer) -> %
      ++ \spad{swapColumns!(m,i,j)} interchanges the \spad{i}th and \spad{j}th
      ++ columns of m. This destructively alters the matrix.
    subMatrix: (%,Integer,Integer,Integer,Integer) -> %
      ++ \spad{subMatrix(x,i1,i2,j1,j2)} extracts the submatrix
      ++ \spad{[x(i,j)]} where the index i ranges from \spad{i1} to \spad{i2}
      ++ and the index j ranges from \spad{j1} to \spad{j2}.
    setsubMatrix!: (%,Integer,Integer,%) -> %
      ++ \spad{setsubMatrix(x,i1,j1,y)} destructively alters the
      ++ matrix x. Here \spad{x(i,j)} is set to \spad{y(i-i1+1,j-j1+1)} for
      ++ \spad{i = i1,...,i1-1+nrows y} and \spad{j = j1,...,j1-1+ncols y}.

--% Arithmetic

    +: (%,%) -> %
      ++ \spad{x + y} is the sum of the matrices x and y.
      ++ Error: if the dimensions are incompatible.
    if R has AbelianGroup then
        -: (%,%) -> %
          ++ \spad{x - y} is the difference of the matrices x and y.
          ++ Error: if the dimensions are incompatible.
        -:  %    -> %
          ++ \spad{-x} returns the negative of the matrix x.
        *: (Integer, %) -> %
          ++ \spad{n * x} is an integer multiple.
    *: (%,%) -> %
      ++ \spad{x * y} is the product of the matrices x and y.
      ++ Error: if the dimensions are incompatible.
    *: (R,%) -> %
      ++ \spad{r*x} is the left scalar multiple of the scalar r and the
      ++ matrix x.
    *: (%,R) -> %
      ++ \spad{x * r} is the right scalar multiple of the scalar r and the
      ++ matrix x.
    *: (%,Col) -> Col
      ++ \spad{x * c} is the product of the matrix x and the column vector c.
      ++ Error: if the dimensions are incompatible.
    *: (Row,%) -> Row
      ++ \spad{r * x} is the product of the row vector r and the matrix x.
      ++ Error: if the dimensions are incompatible.
    -- "^" : (%, PositveInteger) -> %
    positivePower : (%, Integer) -> %
      ++ \spad{positivePower(x, n)} computes a positive integral power of the
      ++ matrix x.  Error: if the matrix is not square.
    if R has Monoid then
        ^: (%, NonNegativeInteger) -> %
          ++ \spad{x ^ n} computes a non-negative integral power of the
          ++ matrix x.  Error: if the matrix is not square.
    if R has IntegralDomain then
      exquo: (%,R) -> Partial %
        ++ \spad{exquo(m,r)} computes the exact quotient of the elements
        ++ of m by r, returning \axiom{"failed"} if this is not possible.
    if R has Field0 then
      /: (%,R) -> %
        ++ \spad{m/r} divides the elements of m by r. Error: if \spad{r = 0}.

--% Linear algebra

--    if R has EuclideanDomain0 then
--      rowEchelon: % -> %
--        ++ \spad{rowEchelon(m)} returns the row echelon form of the matrix m.
--      columnSpace: % -> List Col
--        ++ \spad{columnSpace(m)} returns a sublist of columns of the matrix m
--        ++ forming a basis of its column space

--    if R has IntegralDomain then
--      rank: % -> NonNegativeInteger
--        ++ \spad{rank(m)} returns the rank of the matrix m.
--      nullity: % -> NonNegativeInteger
--        ++ \spad{nullity(m)} returns the nullity of the matrix m. This is
--        ++ the dimension of the null space of the matrix m.
--      nullSpace: % -> List Col
--        ++ \spad{nullSpace(m)} returns a basis for the null space of
--        ++ the matrix m.

--    if R has CommutativeRing then
--      determinant: % -> R
--        ++ \spad{determinant(m)} returns the determinant of the matrix m.
--        ++ Error: if the matrix is not square.
--      minordet: % -> R
--        ++ \spad{minordet(m)} computes the determinant of the matrix m using
--        ++ minors. Error: if the matrix is not square.
--      Pfaffian: % -> R
--        ++ \spad{Pfaffian(m)} returns the Pfaffian of the matrix m.
--        ++ Error: if the matrix is not antisymmetric.

--    if R has Field0 then
--      inverse: % -> Partial %
--        ++ \spad{inverse(m)} returns the inverse of the matrix m.
--        ++ If the matrix is not invertible, "failed" is returned.
--        ++ Error: if the matrix is not square.
--      ^: (%,Integer) -> %
--        ++ \spad{m^n} computes an integral power of the matrix m.
--        ++ Error: if matrix is not square or if the matrix
--        ++ is square but not invertible.
    default
     default x, y, m: %
     default n: NonNegativeInteger
     default a, r: R
     default i1, i2: Integer
     default j1, j2: Integer
     import from UniversalSegment Integer
     minr ==> minRowIndex
     maxr ==> maxRowIndex
     minc ==> minColIndex
     maxc ==> maxColIndex
     mini ==> minIndex
     maxi ==> maxIndex

--% Predicates

     square? x: Boolean == nrows x = ncols x

     diagonal? x: Boolean ==
       not square? x => false
       for i in minr x .. maxr x repeat
         for j in minc x .. maxc x | (j - minc x) ~= (i - minr x) repeat
           not zero? qelt(x, i, j) => return false
       true

     symmetric? x: Boolean ==
       (nRows := nrows x) ~= ncols x => false
       mr := minRowIndex x; mc := minColIndex x
       for i in 0..(nRows - 1) repeat
         for j in (i + 1)..(nRows - 1) repeat
           qelt(x,mr + i,mc + j) ~= qelt(x,mr + j,mc + i) => return false
       true

     if R has AbelianGroup then
         antisymmetric? x: Boolean ==
             (nRows := nrows x) ~= ncols x => false
             mr := minRowIndex x; mc := minColIndex x
             for i in 0..(nRows - 1) repeat
                 for j in i..(nRows - 1) repeat
                     qelt(x, mr + i, mc + j) ~= -qelt(x, mr + j, mc + i) =>
                         return false
             true

--% Creation of matrices

     zero(rows: NNI,cols: NNI): % == new(rows,cols,0)

     matrix(l: List List R): % ==
       import from List R
       null l => new(0,0,0)
       -- error check: this is a top level function
       rows : NonNegativeInteger := 1; cols := # first l
       cols = 0 => error "matrices with zero columns are not supported"
       for ll in rest l repeat
         cols ~= # ll => error "matrix: rows of different lengths"
         rows := rows + 1
       ans := new(rows,cols,0)
       for i in minr(ans)..maxr(ans) for ll in l repeat
         for j in minc(ans)..maxc(ans) for r in ll repeat
           qsetelt!(ans,i,j,r)
       ans

     scalarMatrix(n,r): % ==
       ans := zero(n,n)
       for i in minr(ans)..maxr(ans) for j in minc(ans)..maxc(ans) repeat
         qsetelt!(ans,i,j,r)
       ans

     diagonalMatrix(l: List R): % ==
       n := #l; ans := zero(n,n)
       for i in minr(ans)..maxr(ans) for j in minc(ans)..maxc(ans) _
           for r in l repeat qsetelt!(ans,i,j,r)
       ans

     diagonalMatrix(list: List %): % ==
       rows : NonNegativeInteger := 0
       cols : NonNegativeInteger := 0
       for mat in list repeat
         rows := rows + nrows mat
         cols := cols + ncols mat
       ans := zero(rows,cols)
       loR := minr ans; loC := minc ans
       for mat in list repeat
         hiR := loR + nrows(mat)::Integer - 1; hiC := loC + nrows(mat)::Integer - 1
         for i in loR..hiR for k in minr(mat)..maxr(mat) repeat
           for j in loC..hiC for l in minc(mat)..maxc(mat) repeat
             qsetelt!(ans,i,j,qelt(mat,k,l))
         loR := hiR + 1; loC := hiC + 1
       ans

     coerce(v:Col): % ==
       x := new(#v,1,0)
       one := minc(x)
       for i in minr(x)..maxr(x) for k in mini(v)..maxi(v) repeat
         qsetelt!(x,i,one,qelt(v,k))
       x

     transpose(v:Row): % ==
       x := new(1,#v,0)
       one := minr(x)
       for j in minc(x)..maxc(x) for k in mini(v)..maxi(v) repeat
         qsetelt!(x,one,j,qelt(v,k))
       x

     transpose(x:%): % ==
       ans := new(ncols x,nrows x,0)
       for i in minr(ans)..maxr(ans) repeat
         for j in minc(ans)..maxc(ans) repeat
           qsetelt!(ans,i,j,qelt(x,j,i))
       ans

     squareTop x: % ==
       nrows x < (cols := ncols x) =>
         error "squareTop: number of columns exceeds number of rows"
       ans := new(cols,cols,0)
       for i in minr(x)..(minr(x) + cols::Integer - 1) repeat
         for j in minc(x)..maxc(x) repeat
           qsetelt!(ans,i,j,qelt(x,i,j))
       ans

     horizConcat(x,y): % ==
       (rows := nrows x) ~= nrows y =>
         error "HConcat: matrices must have same number of rows"
       ans := new(rows,(cols := ncols x) + ncols y,0)
       for i in minr(x)..maxr(x) repeat
         for j in minc(x)..maxc(x) repeat
           qsetelt!(ans,i,j,qelt(x,i,j))
       for i in minr(y)..maxr(y) repeat
         for j in minc(y)..maxc(y) repeat
           qsetelt!(ans,i,j + cols::Integer,qelt(y,i,j))
       ans

     vertConcat(x,y): % ==
       (cols := ncols x) ~= ncols y =>
         error "HConcat: matrices must have same number of columns"
       ans := new((rows := nrows x) + nrows y,cols,0)
       for i in minr(x)..maxr(x) repeat
         for j in minc(x)..maxc(x) repeat
           qsetelt!(ans,i,j,qelt(x,i,j))
       for i in minr(y)..maxr(y) repeat
         for j in minc(y)..maxc(y) repeat
           qsetelt!(ans,i + rows::Integer,j,qelt(y,i,j))
       ans

--% Part extraction/assignment

     listOfLists x: List List R ==
       ll : List List R := nil()
       for i in maxr(x)..minr(x) by -1 repeat
         l : List R := nil()
         for j in maxc(x)..minc(x) by -1 repeat
           l := cons(qelt(x,i,j),l)
         ll := cons(l,ll)
       ll

     swapRows!(x,i1,i2): % ==
       (i1 < minr(x)) or (i1 > maxr(x)) or (i2 < minr(x)) or _
           (i2 > maxr(x)) => error "swapRows!: index out of range"
       i1 = i2 => x
       for j in minc(x)..maxc(x) repeat
         r := qelt(x,i1,j)
         qsetelt!(x,i1,j,qelt(x,i2,j))
         qsetelt!(x,i2,j,r)
       x

     swapColumns!(x,j1,j2): % ==
       (j1 < minc(x)) or (j1 > maxc(x)) or (j2 < minc(x)) or _
           (j2 > maxc(x)) => error "swapColumns!: index out of range"
       j1 = j2 => x
       for i in minr(x)..maxr(x) repeat
         r := qelt(x,i,j1)
         qsetelt!(x,i,j1,qelt(x,i,j2))
         qsetelt!(x,i,j2,r)
       x

     elt(x:%,rowList:List Integer,colList:List Integer): % ==
       for ei in rowList repeat
         (ei < minr(x)) or (ei > maxr(x)) =>
           error "elt: index out of range"
       for ej in colList repeat
         (ej < minc(x)) or (ej > maxc(x)) =>
           error "elt: index out of range"
       y := new(# rowList,# colList,0)
       for ei in rowList for i in minr(y)..maxr(y) repeat
         for ej in colList for j in minc(y)..maxc(y) repeat
           qsetelt!(y,i,j,qelt(x,ei,ej))
       y

     setelt(x:%,rowList:List Integer,colList:List Integer,y:%): % ==
       for ei in rowList repeat
         (ei < minr(x)) or (ei > maxr(x)) =>
           error "setelt: index out of range"
       for ej in colList repeat
         (ej < minc(x)) or (ej > maxc(x)) =>
           error "setelt: index out of range"
       ((# rowList) ~= (nrows y)) or ((# colList) ~= (ncols y)) =>
         error "setelt: matrix has bad dimensions"
       for ei in rowList for i in minr(y)..maxr(y) repeat
         for ej in colList for j in minc(y)..maxc(y) repeat
           qsetelt!(x,ei,ej,qelt(y,i,j))
       y

     subMatrix(x,i1,i2,j1,j2): % ==
       (i2 < i1) => error "subMatrix: bad row indices"
       (j2 < j1) => error "subMatrix: bad column indices"
       (i1 < minr(x)) or (i2 > maxr(x)) =>
         error "subMatrix: index out of range"
       (j1 < minc(x)) or (j2 > maxc(x)) =>
         error "subMatrix: index out of range"
       rows := (i2 - i1 + 1) pretend NonNegativeInteger
       cols := (j2 - j1 + 1) pretend NonNegativeInteger
       y := new(rows,cols,0)
       for i in minr(y)..maxr(y) for k in i1..i2 repeat
         for j in minc(y)..maxc(y) for l in j1..j2 repeat
           qsetelt!(y,i,j,qelt(x,k,l))
       y

     setsubMatrix!(x,i1,j1,y): % ==
       i2 := i1 + nrows(y)::Integer -1
       j2 := j1 + ncols(y)::Integer -1
       (i1 < minr(x)) or (i2 > maxr(x)) =>
         error "setsubMatrix!: inserted matrix too big, use subMatrix to restrict it"
       (j1 < minc(x)) or (j2 > maxc(x)) =>
         error "setsubMatrix!: inserted matrix too big, use subMatrix to restrict it"
       for i in minr(y)..maxr(y) for k in i1..i2 repeat
         for j in minc(y)..maxc(y) for l in j1..j2 repeat
           qsetelt!(x,k,l,qelt(y,i,j))
       x

--% Arithmetic

     x + y: % ==
       ((rc := nrows x) ~= nrows(y)) or ((c := ncols x) ~= ncols y) =>
         error "can't add matrices of different dimensions"
       ans := new(rc,c,0)
       for i in minr(x)..maxr(x) repeat
         for j in minc(x)..maxc(x) repeat
           qsetelt!(ans,i,j,qelt(x,i,j) + qelt(y,i,j))
       ans

     if R has AbelianGroup then
         x - y: % ==
             ((rc := nrows x) ~= nrows y) or ((c := ncols x) ~= ncols y) =>
                 error "can't subtract matrices of different dimensions"
             ans := new(rc, c, 0)
             for i in minr(x)..maxr(x) repeat
                 for j in minc(x)..maxc(x) repeat
                     qsetelt!(ans, i, j, qelt(x, i, j) - qelt(y, i, j))
             ans

         - x: % == map((r1 : R) : R +-> - r1, x)
         (i1:Integer) * (x:%): % == map((r1 : R) : R +-> i1 * r1, x)

     (a:R) * (x:%): % == map((r1: R): R +-> a * r1,x)
     (x:%) * (a:R): % == map((r1: R): R +-> r1 * a,x)

     (x:%) * (y:%): % ==
       (ncols x ~= nrows y) =>
         error "can't multiply matrices of incompatible dimensions"
       ans := new(nrows x,ncols y,0)
       for i in minr(x)..maxr(x) repeat
         for j in minc(y)..maxc(y) repeat
           entry :=
             sum : R := 0
             for k in minr(y)..maxr(y) for l in minc(x)..maxc(x) repeat
               sum := sum + qelt(x,i,l) * qelt(y,k,j)
             sum
           qsetelt!(ans,i,j,entry)
       ans

     -- positivePower:(%,Integer) -> %
     positivePower(x,i1): % ==
--       one? i1 => x
       (i1 = 1) => x
       odd? i1 => x * positivePower(x,i1 - 1)
       y := positivePower(x,i1 quo 2)
       y * y

     if R has Monoid then
         (x:%) ^ (n:NonNegativeInteger): % ==
             not((nn := nrows x) = ncols x) => error "^: matrix must be square"
             zero? n => scalarMatrix(nn, 1)
             positivePower(x, n::Integer)

     --if R has ConvertibleTo InputForm then
       --convert(x:%):InputForm ==
         --convert [convert('matrix)@InputForm,
                  --convert listOfLists x]$List(InputForm)

     if Col has shallowlyMutable then

       (x:%) * (v:Col): Col ==
         ncols(x) ~= #v =>
           error "can't multiply matrix A and vector v if #cols A ~= #v"
         w : Col := new(nrows x,0)
         for i in minr(x)..maxr(x) for k in mini(w)..maxi(w) repeat
           w.k :=
             sum : R := 0
             for j in minc(x)..maxc(x) for l in mini(v)..maxi(v) repeat
               sum := sum + qelt(x,i,j) * v(l)
             sum
         w

     if Row has shallowlyMutable then

       (v:Row) * (x:%): Row ==
         nrows(x) ~= #v =>
           error "can't multiply vector v and matrix A if #rows A ~= #v"
         w : Row := new(ncols x,0)
         for j in minc(x)..maxc(x) for k in mini(w)..maxi(w) repeat
           w.k :=
             sum : R := 0
             for i in minr(x)..maxr(x) for l in mini(v)..maxi(v) repeat
               sum := sum + qelt(x,i,j) * v(l)
             sum
         w

     if R has IntegralDomain then
       x exquo a: Partial % ==
         import from Partial R
         ans := new(nrows x,ncols x,0)
         for i in minr(x)..maxr(x) repeat
           for j in minc(x)..maxc(x) repeat
             entry :=
               failed?(pr := (qelt(x,i,j) exquo a))  =>
                 return failed()
               pr :: R
             qsetelt!(ans,i,j,entry)
         success(ans)

     if R has Field0 then
       x / r: % == map((r1: R): R +-> r1 / r,x)

--       (x:%) ^ (i1:Integer): % ==
--         import from Partial %
--         not((nn:= nrows x) = ncols x) => error "^: matrix must be square"
--         zero? i1 => scalarMatrix(nn,1)
--         positive? i1 => positivePower(x,i1)
--         failed?(xInv := inverse x)  =>
--           error "^: matrix must be invertible"
--         positivePower(xInv :: %,-i1)


--\subsection{columnSpace}
--\verb|columnSpace| extracts from the columns of $M$ a basis for the space they
--generate.  The columns of $M$ that generate the space correspond to those
--columns in the row echelon form of $M$ whose last non-zero entry is the first
--non-zero entry in a row.  As an example, let $M$ be the matrix
--\begin{verbatim}
--         +2  1  0  2+
--         |          |
--         |2  0  3  0|
--         |          |
--         +2  1  0  1+
--\end{verbatim}
--Its row-echelon form is
--\begin{verbatim}
--         +2  0   3   0+
--         |            |
--         |0  1  - 3  0|
--         |            |
--         +0  0   0   1+
--\end{verbatim}
--And indeed, \verb|@[[2,2,2],[1,0,1],[2,0,1]]| is a $\mathbb Q$-basis of the
--column space.  Reversing the extracted columns is not strictly necessary, but
--makes the result look more natural.
--
--Note that selecting the non-zero rows of the row echelon form of the transposed
--matrix would give another basis of the column space.
--
--<<category MATCAT MatrixCategory>>=
--     if R has EuclideanDomain then
--        columnSpace M ==
--            M2 := rowEchelon M
--            basis: List Col := []
--            n: Integer := ncols M
--            m: Integer := nrows M
--            indRow: Integer := 1
--            for k in 1..n while indRow <= m repeat
--                if not zero?(M2.(indRow, k)) then
--                    basis := cons(column(M, k), basis)
--                    indRow := indRow + 1
--            reverse! basis
--
--@
--
--<<TEST MATCAT>>=
--testcase "columnSpace"
--M := matrix [[1,2,3],[4,5,6],[7,8,9],[1,1,1]];
--testEquals("columnSpace M", "[[1,4,7,1],[2,5,8,1]]")
--testEquals("columnSpace transpose M", "[[1,2,3],[4,5,6]]")
--testEquals("columnSpace [[0,0]]", "[]")
--testEquals("columnSpace(M::RMATRIX(4,3,INT))", _
--           "[[1,4,7,1],[2,5,8,1]]::List DIRPROD(4, INT)")
--@
--
--\subsection{Pfaffian}
--We compute the Pfaffian of an antisymmetric matrix using an algorithm by
--G\"unter Ziegler\cite{1}.  I did not check whether we really need commutative
--multiplication.
--
--\verb|B0| could be dubbed \emph{skew symmetric unit matrix}:
--<<category MATCAT MatrixCategory>>=
--
--     if R has CommutativeRing then
--        B0(n: PositiveInteger): % ==
--            matrix [[(if i=j+1 and odd? j _
--                      then -1 _
--                      else if i=j-1 and odd? i _
--                           then 1 _
--                           else 0) for j in 1..n] for i in 1..n]
--
--@
--\verb|PfChar| is the \emph{Pfaffian-characteristic polynomial} denoted $\tilde
--P_A$ in Rote's article.  Note that there is a misprint in the article,
--Formula~(22), the generating function for alternating clow sequences with head
--$1$ according to length, should read
--\begin{equation}
--  G(\lambda)=\lambda^2+a_{12}+rB_0s\lambda^{-2}+rB_0MB_0s\lambda^{-4}+
--             rB_0MB_0MB_0s\lambda^{-6}+\dots,
--\end{equation}
--i.e., the coefficient of $\lambda^2$ is $+1$, not $-1$.
--
--With this definition, we have (Equation~(23) in Rote's article)
--\begin{equation}
--  \tilde P_A(\lambda) = G(\lambda) \tilde P_M(\lambda),
--\end{equation}
--where we split $A$ as follows:
--\begin{equation}
--  A=\left(
--  \begin{array}{cc|c}
--    0       & a_{12} & r\\
--    -a_{12} & 0      & -s^t\\
--    \hline
--    -r^t    & s      & M
--  \end{array}\right).
--\end{equation}
--<<category MATCAT MatrixCategory>>=
--        SUPR ==> SparseUnivariatePolynomial R
--        PfChar(A: %): SUPR ==
--            n := nrows A
--            (n = 2) => monomial(1$R,2)$SUPR + qelt(A, 1, 2)::SUPR
--            M := subMatrix(A, 3, n, 3, n)
--            r := subMatrix(A, 1, 1, 3, n)
--            s := subMatrix(A, 3, n, 2, 2)
--
--            p := PfChar M
--            d := degree(p)$SUPR
--
--            B := B0((n-2)::PositiveInteger)
--            C := r*B
--            g: List R := [qelt(C*s,1,1), qelt(A,1,2), 1]
--            if d >= 4 then
--                B := M*B
--                for i in 4..d by 2 repeat
--                    C := C*B
--                    g := cons(qelt(C*s,1,1), g)
--            g := reverse! g
--
--            res: SUPR := 0
--            for i in 0..d by 2 for j in 2..d+2 repeat
--                c := coefficient(p, i)
--                for e in first(g, j) for k in 2..-d by -2 repeat
--                    res := res + _
--                           monomial(c * e, (k+i)::NonNegativeInteger)$SUPR
--
--            res
--
--@
--The Pfaffian is the constant term of the \emph{Pfaffian-characteristic
--  polynomial}:
--<<category MATCAT MatrixCategory>>=
--        Pfaffian A ==
--            if antisymmetric? A
--            then if odd? nrows A
--                 then 0
--                 else PfChar(A).0
--            else error "Pfaffian: only defined for antisymmetric square matrices!"
--@
--
--<<TEST MATCAT>>=
--testcase "Pfaffian"
--m n == matrix [[(if i = j then 0 _
--                          else if i < j _
--                               then x[i,j] _
--                               else -x[j,i]) for i in 1..n] for j in 1..n]
--testEquals("Pfaffian [[0,1,0,0],[-1,0,0,0],[0,0,0,1],[0,0,-1,0]]", "1")
--testEquals("Pfaffian [[0, u, v, w],[-u, 0, x, y],[-v,-x,0,z],[-w,-y,-z,0]]", _
--           "u*z-v*y+w*x")
--testEquals("Pfaffian m 3", "0")
--testEquals("Pfaffian [[0,0],[0,0]]", "0")
--M := m 6;
--testEquals("(Pfaffian M)^2", "determinant M")
--testLibraryError "Pfaffian [[1,2],[0,0]]"
--testLibraryError "Pfaffian [[1,2,3],[0,0,0]]"
--
--@
--
--<<category MATCAT MatrixCategory>>=
--