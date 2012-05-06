--DEPS: SetCategory Partial Reference OrderedSet
#include "axiom.as"

#pile
import from System
import from String

UserDefinedPartialOrdering(S:SetCategory): with
  setOrder    : List S -> ()
    ++ setOrder([a1,...,an]) defines a partial ordering on S given by:
    ++    (1)  \spad{a1 < a2 < ... < an}.
    ++    (2)  \spad{b < ai   for i = 1..n} and b not among the ai's.
    ++    (3)  undefined on \spad{(b, c)} if neither is among the ai's.
  setOrder    : (List S, List S) -> ()
    ++ setOrder([b1,...,bm], [a1,...,an]) defines a partial
    ++ ordering on S given by:
    ++    (1)  \spad{b1 < b2 < ... < bm < a1 < a2 < ... < an}.
    ++    (2)  \spad{bj < c < ai}  for c not among the ai's and bj's.
    ++    (3)  undefined on \spad{(c,d)} if neither is among the ai's,bj's.
  getOrder    : () -> Record(low: List S, high: List S)
    ++ getOrder() returns \spad{[[b1,...,bm], [a1,...,an]]} such that the
    ++ partial ordering on S was given by
    ++ \spad{setOrder([b1,...,bm],[a1,...,an])}.
  less?       : (S, S) -> Partial Boolean
    ++ less?(a, b) compares \spad{a} and b in the partial ordering induced by
    ++ setOrder.
  less?       : (S, S, (S, S) -> Boolean) -> Boolean
    ++ less?(a, b, fn) compares \spad{a} and b in the partial ordering induced
    ++ by setOrder, and returns \spad{fn(a, b)} if \spad{a}
    ++ and b are not comparable
    ++ in that ordering.
  largest     : (List S, (S, S) -> Boolean) -> S
    ++ largest(l, fn) returns the largest element of l where the partial
    ++ ordering induced by setOrder is completed into a total one by fn.
  userOrdered?: () -> Boolean
    ++ userOrdered?() tests if the partial ordering induced by
    ++ \spadfunFrom{setOrder}{UserDefinedPartialOrdering} is not empty.
  if S has OrderedSet then
    largest: List S -> S
      ++ largest l returns the largest element of l where the partial
      ++ ordering induced by setOrder is completed into a total one by
      ++ the ordering on S.
    more?  : (S, S) -> Boolean
      ++ more?(a, b) compares \spad{a} and b in the partial ordering induced
      ++ by setOrder, and uses the ordering on S if \spad{a} and b are not
      ++ comparable in the partial ordering.

 == add
  default l, h: List S
  default a, b: S
  import from Reference List S;
  import from List S;

  llow :Reference List S := _ref nil()
  lhigh:Reference List S := _ref nil()

  userOrdered?(): Boolean == not(empty? deref llow) or not(empty? deref lhigh)
  getOrder(): Record(low: List S, high: List S)  == [deref llow, deref lhigh]
  setOrder l: ()     == setOrder(nil(), l)

  setOrder(l, h): () ==
    setref(llow, removeDuplicates l)
    setref(lhigh, removeDuplicates h)

  less?(a, b, f: (S, S) -> Boolean): Boolean ==
    import from Partial Boolean
    failed?(u := less?(a, b)) => f(a, b)
    u::Boolean

  largest(x: List S, f: (S, S) -> Boolean): S ==
    empty? x => error "largest: empty list"
    empty? rest x => first x
    a := largest(rest x, f)
    less?(first x, a, f) => a
    first x

  less?(a, b): Partial Boolean ==
    for x in deref llow repeat
      x = a => return success(a ~= b)
      x = b => return success(false)
    aa := bb := false$Boolean
    for x in deref lhigh repeat
      if x = a then
        bb => return success(false)
        aa := true
      if x = b then
        aa => return success(a ~= b)
        bb := true
    aa => success(false)
    bb => success(true)
    failed();

  if S has OrderedSet then
    more?(a, b): Boolean == not less?(a, b, (y: S, z: S): Boolean +-> y < z)
    largest(x: List S): S   == largest(x, (y: S, z: S): Boolean +-> y < z)
