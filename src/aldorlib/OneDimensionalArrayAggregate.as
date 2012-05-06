--DEPS: FiniteLinearAggregate shallowlyMutable Fold
--DEPS: UniversalSegment FiniteLinearAggregateSort Integer_OrderedRing

#include "axiom.as"
#pile
import from Boolean
import from System
import from String

OneDimensionalArrayAggregate(S:Type): Category 
 ==  Join(FiniteLinearAggregate S, shallowlyMutable)
  with
   default
    import from UniversalSegment Integer
    import from Integer

    default x, y, a, b: %
    default f: S -> Boolean
    default f2: (S, S) -> Boolean

    default identity, absorber: S

    parts x: List S       == [qelt(x, i) for i in minIndex x .. maxIndex x]
    sort!(f2, a): % == quickSort(f2, a)$FiniteLinearAggregateSort(S, %)

    any?(f, a): Boolean ==
      for i in minIndex a .. maxIndex a repeat
        f qelt(a, i) => return true
      false

    every?(f, a): Boolean ==
      for i in minIndex a .. maxIndex a repeat
        not(f qelt(a, i)) => return false
      true

    position(f:S -> Boolean, a:%): Integer ==
      for i in minIndex a .. maxIndex a repeat
        f qelt(a, i) => return i
      minIndex(a) - 1

    find(f, a): Partial S ==
      for i in minIndex a .. maxIndex a repeat
        f qelt(a, i) => return success(qelt(a, i))
      failed()

    count(f:S->Boolean, a:%): Integer ==
      n:NonNegativeInteger := 0
      for i in minIndex a .. maxIndex a repeat
        if f(qelt(a, i)) then n := n+1
      n::Integer
      
    default mf: S -> S
    map!(mf, a): % ==
      for i in minIndex a .. maxIndex a repeat
        qsetelt!(a, i, mf qelt(a, i))
      a

    setelt(a:%, s:UniversalSegment(Integer), e:S): S ==
      l := lo s; h := if hasHi s then hi s else maxIndex a
      l < minIndex a or h > maxIndex a => error "index out of range"
      for k in l..h repeat qsetelt!(a, k, e)
      e

    default rf: (S, S) -> S
    reduce(rf, a): S ==
      empty? a => error "cannot reduce an empty aggregate"
      r := qelt(a, m := minIndex a)
      for k in m+1 .. maxIndex a repeat r := rf(r, qelt(a, k))
      r

    reduce(rf, a, identity): S ==
      for k in minIndex a .. maxIndex a repeat
        identity := rf(identity, qelt(a, k))
      identity

    if S has SetCategory then
       reduce(rf, a, identity, absorber):  S ==
         for k in minIndex a .. maxIndex a while identity ~= absorber
                repeat identity := rf(identity, qelt(a, k))
         identity

-- this is necessary since new has disappeared.
    --local stupidnew: (NonNegativeInteger, %, %) -> %
    --local stupidget: List % -> S

-- a and b are not both empty if n > 0
    local stupidnew(n: NonNegativeInteger, a, b): % ==
      zero? n => empty()
      new(n, (empty? a => qelt(b, minIndex b); qelt(a, minIndex a)))

-- at least one element of l must be non-empty
    local stupidget(l: List %): S ==
      for a in l repeat
        not empty? a => return first a
      error "Should not happen"

    default map2: (S, S) -> S
    map(map2, a, b): % ==
      m := max(minIndex a, minIndex b)
      n := min(maxIndex a, maxIndex b)
      l := max(0, n - m + 1)::NonNegativeInteger
      c := stupidnew(l, a, b)
      for i in minIndex(c).. for j in m..n repeat
        qsetelt!(c, i, map2(qelt(a, j), qelt(b, j)))
      c

--  map(f, a, b, x) ==
--    m := min(minIndex a, minIndex b)
--    n := max(maxIndex a, maxIndex b)
--    l := (n - m + 1)::NonNegativeInteger
--    c := new l
--    for i in minIndex(c).. for j in m..n repeat
--      qsetelt!(c, i, f(a(j, x), b(j, x)))
--    c

    merge(f2, a, b): % ==
      import from NonNegativeInteger
      r := stupidnew(#a + #b, a, b)
      i := minIndex a
      m := maxIndex a
      j := minIndex b
      n := maxIndex b
      local k: Integer := 0
      for free k in minIndex(r).. while i <= m and j <= n repeat
        if f2(qelt(a, i), qelt(b, j)) then
          qsetelt!(r, k, qelt(a, i))
          i := i+1
        else
          qsetelt!(r, k, qelt(b, j))
          j := j+1
      for free k in k.. for free i in i..m repeat qsetelt!(r, k, elt(a, i))
      for free k in k.. for free j in j..n repeat qsetelt!(r, k, elt(b, j))
      r

    elt(a:%, s:UniversalSegment(Integer)): % ==
      l := lo s
      h := if hasHi s then hi s else maxIndex a
      l < minIndex a or h > maxIndex a => error "index out of range"
      r := stupidnew(max(0, h - l + 1)::NonNegativeInteger, a, a)
      for k in minIndex r.. for i in l..h repeat
        qsetelt!(r, k, qelt(a, i))
      r

    insert(a:%, b:%, i:Integer): % ==
      import from NonNegativeInteger
      m := minIndex b
      n := maxIndex b
      i < m or i > n => error "index out of range"
      y := stupidnew(#a + #b, a, b)
      local k: Integer := 0
      for free k in minIndex y.. for j in m..i-1 repeat
        qsetelt!(y, k, qelt(b, j))
      for free k in k.. for j in minIndex a .. maxIndex a repeat
        qsetelt!(y, k, qelt(a, j))
      for free k in k.. for j in i..n repeat qsetelt!(y, k, qelt(b, j))
      y

    copy x: % ==
      y := stupidnew(#x, x, x)
      for i in minIndex x .. maxIndex x for j in minIndex y .. repeat
        qsetelt!(y, j, qelt(x, i))
      y

    copyInto!(y, x, s: Integer): % ==
      import from NonNegativeInteger
      s < minIndex y or s + #x::Integer > maxIndex y + 1 =>
                                              error "index out of range"
      for i in minIndex x .. maxIndex x for j in s.. repeat
        qsetelt!(y, j, qelt(x, i))
      y

    construct(l: List S): %==
--    a := new(#l)
      empty? l => empty()
      a := new(#l, first l)
      for i in minIndex(a).. for xs in l repeat qsetelt!(a, i, xs)
      a

    delete(a:%, s:UniversalSegment(Integer)): % ==
      import from NonNegativeInteger
      l := lo s; h := if hasHi s then hi s else maxIndex a
      l < minIndex a or h > maxIndex a => error "index out of range"
      h < l => copy a
      r := stupidnew((#a::Integer - h + l - 1)::NonNegativeInteger, a, a)
      local k: Integer := 0
      for free k in minIndex(r).. for i in minIndex a..l-1 repeat
        qsetelt!(r, k, qelt(a, i))
      for free k in k.. for i in h+1 .. maxIndex a repeat
        qsetelt!(r, k, qelt(a, i))
      r

    delete(x:%, i:Integer): % ==
      import from NonNegativeInteger
      i < minIndex x or i > maxIndex x => error "index out of range"
      y := stupidnew((#x - 1$NonNegativeInteger)::NonNegativeInteger, x, x)
      for free i in minIndex(y).. for j in minIndex x..i-1 repeat
        qsetelt!(y, i, qelt(x, j))
      for free i in i .. for j in i+1 .. maxIndex x repeat
        qsetelt!(y, i, qelt(x, j))
      y

    reverse!(x): % ==
      m := minIndex x
      n := maxIndex x
      for i in 0..((n-m) quo 2) repeat swap!(x, m+i, n-i)
      x

    concat(l: List %): % ==
      import from Fold NonNegativeInteger
      import from List NonNegativeInteger
      empty? l => empty()
      n: NonNegativeInteger := _+/[#a for a in l]
      i := minIndex(r := new(n, stupidget l))
      for a in l repeat
        copyInto!(r, a, i)
        i := i + #a::Integer
      r

    sorted?(f2, a): Boolean ==
      for i in minIndex(a)..maxIndex(a)-1 repeat
        not f2(qelt(a, i), qelt(a, i + 1)) => return false
      true

    concat(x:%, y:%): % ==
      import from NonNegativeInteger
      z := stupidnew(#x + #y, x, y)
      copyInto!(z, x, i := minIndex z)
      copyInto!(z, y, i + #x::Integer)
      z

    if S has CoercibleTo(OutputForm) then
        coerce(r:%):OutputForm ==
	    import from List OutputForm
            bracket commaSeparate(
              [qelt(r, k)::OutputForm for k in minIndex r .. maxIndex r])

    if S has SetCategory then
      x = y: Boolean ==
        import from NonNegativeInteger
        #x ~= #y => false
        for i in minIndex x .. maxIndex x repeat
          not(qelt(x, i) = qelt(y, i)) => return false
        true

      position(xs:S, t:%, s:Integer): Integer ==
        n := maxIndex t
        s < minIndex t or s > n => error "index out of range"
        for k in s..n repeat
          qelt(t, k) = xs => return k
        minIndex(t) - 1

    if S has OrderedSet then
      a < b: Boolean ==
        import from NonNegativeInteger
        for i in minIndex a .. maxIndex a
          for j in minIndex b .. maxIndex b repeat
            qelt(a, i) ~= qelt(b, j) => return a.i < b.j
        #a < #b

