--DEPS: OneDimensionalArrayAggregate RadicalCategory Matrix_TwoDimensionalArrayCategory

#include "axiom.as"

#pile
import from Boolean
import from System
import from String

VectorCategory(R:Type): Category == OneDimensionalArrayAggregate R with
    if R has AbelianSemiGroup then
      _+ : (%, %) -> %
        ++ x + y returns the component-wise sum of the vectors x and y.
        ++ Error: if x and y are not of the same length.
    if R has AbelianMonoid then
      zero: NonNegativeInteger -> %
        ++ zero(n) creates a zero vector of length n.
    if R has AbelianGroup then
      - : % -> %
        ++ -x negates all components of the vector x.
      - : (%, %) -> %
        ++ x - y returns the component-wise difference of the vectors x and y.
        ++ Error: if x and y are not of the same length.
      * : (Integer, %) -> %
        ++ n * y multiplies each component of the vector y by the integer n.
    if R has Monoid then
      * : (R, %) -> %
        ++ r * y multiplies the element r times each component of the vector y.
      * : (%, R) -> %
        ++ y * r multiplies each component of the vector y by the element r.
    if R has Ring then
      dot: (%, %) -> R
        ++ dot(x,y) computes the inner product of the two vectors x and y.
        ++ Error: if x and y are not of the same length.
      outerProduct: (%, %) -> Matrix R
        ++ outerProduct(u,v) constructs the matrix whose (i,j)'th element is
        ++ u(i)*v(j).
      cross: (%, %) -> %
        ++ cross(u,v) constructs the cross product of u and v.
        ++ Error: if u and v are not of length 3.
    if R has RadicalCategory and R has Ring then
      length: % -> R
        ++ length(v) computes the sqrt(dot(v,v)), i.e. the magnitude
      magnitude: % -> R
        ++ magnitude(v) computes the sqrt(dot(v,v)), i.e. the length
    default
     default u, v: %
     default n: NonNegativeInteger
     import from R

     if R has AbelianSemiGroup then
      u + v: % ==
        import from NonNegativeInteger
        #u ~= #v => error "Vectors must be of the same length"
        map(+ , u, v)

     if R has AbelianMonoid then
      zero n: % == new(n, 0)

     if R has AbelianGroup then
      -(u: %): %                 == map((x: R): R +-> - x, u)
      (i : Integer) * (u : %): % == map((x: R): R +-> i*x, u)
      u - v: %           == u + (-v)

     if R has Monoid then
      (u : %) * (r : R): %       == map((x: R): R +-> x*r, u)
      (r : R) * (u : %): %       == map((x: R): R +-> r*x, u)

     if R has Ring then
      import from Fold R, List R, UniversalSegment Integer
      dot(u, v): R ==
        #u ~= #v => error "Vectors must be of the same length"
        (+)/[qelt(u, i) * qelt(v, i) for i in minIndex u .. maxIndex u]

      outerProduct(u, v): Matrix R ==
        import from List List R, List R
        zz := [[qelt(u, i) * qelt(v,j) for i in minIndex u .. maxIndex u] _
                for j in minIndex v .. maxIndex v]
	matrix zz

      cross(u, v): % ==
        NNI==> NonNegativeInteger
        import from Integer, NonNegativeInteger
        #u ~= 3::NNI or #v ~= 3::NNI => error "Vectors must be of length 3"
        construct [qelt(u, 2)*qelt(v, 3) - qelt(u, 3)*qelt(v, 2) , _
                   qelt(u, 3)*qelt(v, 1) - qelt(u, 1)*qelt(v, 3) , _
                   qelt(u, 1)*qelt(v, 2) - qelt(u, 2)*qelt(v, 1) ]

     if R has RadicalCategory and R has Ring then
      length(p: %): R ==
         sqrt(dot(p,p))
      magnitude(p: %): R ==
         sqrt(dot(p,p))

