--DEPS: PrimitiveArray ExtensibleLinearAggregate
#include "axiom.as"

#pile
import from String
import from System

IndexedFlexibleArray(S:Type, mn: Integer): Exports == Implementation where
  A ==> PrimitiveArray S
  I ==> Integer
  N ==> NonNegativeInteger
  U ==> UniversalSegment Integer
  Exports ==>
    Join(OneDimensionalArrayAggregate S,ExtensibleLinearAggregate S) with
      flexibleArray : List S -> %
        ++ flexibleArray(l) creates a flexible array from the list of elements l
      physicalLength : % -> NonNegativeInteger
        ++ physicalLength(x) returns the number of elements x can accomodate before growing
      physicalLength!: (%, I) -> %
        ++ physicalLength!(x,n) changes the physical length of x to be n and returns the new array.
      shrinkable: Boolean -> Boolean
        ++ shrinkable(b) sets the shrinkable attribute of flexible arrays to b and returns the previous value
      removeRepeats! : % -> %
        ++ removeRepeats!(u) destructively replaces runs of consequtive
        ++ equal elements of u by single elements.

  Implementation ==> add
    Rep == Record(physLen:I, logLen:I, f:A)
    default r: %
    import from UniversalSegment I
    import from Rep
    import from I
    import from N
    import from S

    shrinkable? : Boolean := true

    local apply(r, zzz: 'logLen'): I == rep(r).logLen
    local apply(r, zzz: 'physLen'): I == rep(r).physLen
    local apply(r, zzz: 'f'): A == rep(r).f

    local set!(r, zzz: 'logLen', i: I): I == rep(r).logLen := i
    local set!(r, zzz: 'physLen', i: I): I == rep(r).physLen := i
    local set!(r, zzz: 'f', a: A): A == rep(r).f := a

    physicalLength(r): NonNegativeInteger == (r.physLen) pretend NonNegativeInteger

    physicalLength!(r, n: I): % ==
       r.physLen = 0  => error "flexible array must be non-empty"
       growWith(r, n, r.f.0)

    empty(): %   == per [0, 0, empty()]
    #r: N == (r.logLen)::N
    fill!(r, x: S): % == (fill!(r.f, x); r)
    maxIndex r: Integer  == r.logLen - 1 + mn
    minIndex r: Integer   == mn
    new(n: N, a: S): %    == per [n::I, n::I, new(n, a)]

    shrinkable(b: Boolean): Boolean ==
      oldval := shrinkable?
      free shrinkable? := b
      oldval

    flexibleArray(l: List S): % ==
       n := #l
       n = 0 => empty()
       x := first l
       a: % := new(n,x)
       for i in mn + 1..mn + n::I - 1 for y in rest l repeat a.i := y
       a

    -- local utility operations
    newa(n: N, a: A): A ==
       zero? n => empty()
       new(n, a.0)

    growAdding(r: %, b: I, s: %): % ==
       b = 0 => r
       #r > 0 => growAndFill(r, b, (r.f).0)
       #s > 0 => growAndFill(r, b, (s.f).0)
       error "no default filler element"

    growAndFill(r: %, b: I, x: S): % ==
       (r.logLen := r.logLen + b) <= r.physLen => r
       -- enlarge by 50% + b
       n := r.physLen + r.physLen quo 2 + 1
       if r.logLen > n then n := r.logLen
       growWith(r, n, x)

    growWith(r: %, n: I, x: S): % ==
       y := new(n::N, x)$PrimitiveArray(S)
       a := r.f
       for k in 0 .. r.physLen-1 repeat y.k := a.k
       r.physLen := n
       r.f := y
       r

    shrink(r: %, i: I): % ==
       r.logLen := r.logLen - i
       negative?(n := r.logLen) => error "internal bug in flexible array"
       2*n+2 > r.physLen => r
       not shrinkable? => r
       if n < r.logLen then error "cannot shrink flexible array to indicated size"
       n = 0 => empty()
       r.physLen := n
       y := newa(n::N, a := r.f)
       for k in 0 .. n-1 repeat y.k := a.k
       r.f := y
       r

    copy r: % ==
       n := #r
       a := r.f
       v := newa(n, a := r.f)
       for k in 0..n-1 repeat v.k := a.k
       per [n::I, n::I, v]


    elt(r:%, i:I): S ==
       i < mn or i >= r.logLen + mn =>
           error "index out of range"
       r.f.(i-mn)

    setelt(r:%, i:I, x:S): S ==
       i < mn or i >= r.logLen + mn =>
           error "index out of range"
       r.f.(i-mn) := x

    -- operations inherited from extensible aggregate
    merge(g: (S, S) -> Boolean, a: %, b: %): %   == merge!(g, copy a, b)
    concat(x:S, r:%): % == insert!(x, r, mn)

    concat!(r:%, x:S): % ==
       growAndFill(r, 1, x)
       r.f.(r.logLen-1) := x
       r

    concat!(a:%, b:%): % ==
       if eq?(a, b) then b := copy b
       n := #a
       growAdding(a, #b::I, b)
       copyInto!(a, b, n::I + mn)

    remove!(g:(S->Boolean), a:%): % ==
       k:I := 0
       for i in 0..maxIndex a - mn repeat
          if not g(a.i) then (a.k := a.i; k := k+1)
       shrink(a, #a::I - k)

    delete!(r:%, i1:I): % ==
       i := i1 - mn
       i < 0 or i > r.logLen => error "index out of range"
       for k in i..r.logLen-2 repeat r.f.k := r.f.(k+1)
       shrink(r, 1)

    delete!(r:%, i:U): % ==
       l := lo i - mn; m := maxIndex r - mn
       h := (hasHi i => hi i - mn; m)
       l < 0 or h > m => error "index out of range"
       for j in l.. for k in h+1..m repeat r.f.j := r.f.k
       shrink(r, max(0,h-l+1))

    insert!(x:S, r:%, i1:I):% ==
       i := i1 - mn
       n := r.logLen
       i < 0 or i > n => error "index out of range"
       growAndFill(r, 1, x)
       for k in n-1 .. i by -1 repeat r.f.(k+1) := r.f.k
       r.f.i := x
       r

    insert!(a:%, b:%, i1:I):% ==
       i := i1 - mn
       if eq?(a, b) then b := copy b
       m := #a; n := #b
       i < 0 or i > n::I => error "index out of range"
       growAdding(b, m::I, a)
       for k in n-1 .. i by -1 repeat b.f.(m::I+k) := b.f.k
       for k in m-1 .. 0 by -1 repeat b.f.(i+k) := a.f.k
       b

    merge!(g: (S, S) -> Boolean, a: %, b: %): % ==
       m := #a; n := #b; growAdding(a, n::I, b)
       for i in m-1..0 by -1 for j in m+n-1.. by -1 repeat a.f.j := a.f.i
       i := n::I; j: I := 0
       k: I := 0
       for free k in 0.. while i < n::I+m::I and j < n::I repeat
          if g(a.f.i,b.f.j) then (a.f.k := a.f.i; i := i+1)
          else (a.f.k := b.f.j; j := j+1)
       for free k in k.. for free j in j..n-1 repeat a.f.k := b.f.j
       a

    select!(g:(S->Boolean), a:%): % ==
       k:I := 0
       for i in 0..maxIndex a - mn repeat if g(a.f.i) then (a.f.k := a.f.i;k := k+1)
       shrink(a, #a::I - k)

    if S has SetCategory then
      removeDuplicates!(a: %): % ==
         ct: I := #a::I
         ct < 2 => a

         i     := mn
         nlim  := mn + ct
         nlim0 := nlim
         while i < nlim repeat
            j := i+1
            for k in j..nlim-1 | a.k ~= a.i repeat
                a.j := a.k
                j := j+1
            nlim := j
            i := i+1
         nlim ~= nlim0 => delete!(a, i..)
         a

      removeRepeats!(a: %): % ==
          ct := #a::I
          ct < 2 => a

          j := mn
          nlim := mn + ct
          t := a(j)
          i := j + 1
          while i < nlim repeat
              s := a(i)
              if s ~= t then
                  j := j + 1
                  a(j) := (t := s)
              i := i + 1
          j + 1 < nlim => delete!(a, (j + 1)..)
          a

