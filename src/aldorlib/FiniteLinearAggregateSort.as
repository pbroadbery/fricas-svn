--DEPS: FiniteLinearAggregate shallowlyMutable UniversalSegment
#include "axiom.as"

#pile

import from Boolean
import from System
import from String

I ==> Integer
B ==> Boolean
FiniteLinearAggregateSort(S: Type, V: Join(FiniteLinearAggregate(S), shallowlyMutable)): 
  with
    quickSort: ((S, S) -> Boolean, V) -> V
      ++ quickSort(f, agg) sorts the aggregate agg with the ordering function
      ++ f using the quicksort algorithm.
    heapSort : ((S, S) -> Boolean, V) -> V
      ++ heapSort(f, agg) sorts the aggregate agg with the ordering function
      ++ f using the heapsort algorithm.
    shellSort: ((S, S) -> Boolean, V) -> V
      ++ shellSort(f, agg) sorts the aggregate agg with the ordering function
      ++ f using the shellSort algorithm.

 == add
    import from UniversalSegment Integer
    import from Integer
    default r: V
    default n: Integer
    default l: (S, S) -> Boolean
    default i, j, k: I
    
    --local siftUp   : ((S, S) -> B, V, I, I) -> ()
    --local partition: ((S, S) -> B, V, I, I, I) -> I
    --local QuickSort: ((S, S) -> B, V, I, I) -> V

    quickSort(l, r): V == QuickSort(l, r, minIndex r, maxIndex r)

    siftUp(l, r, i, n): () ==
      t := qelt(r, i)
      while (j := 2*i+1) < n repeat
        if (k := j+1) < n and l(qelt(r, j), qelt(r, k)) then j := k
        if l(t,qelt(r,j)) then
           qsetelt!(r, i, qelt(r, j))
           qsetelt!(r, j, t)
           i := j
        else break

    heapSort(l, r): V ==
      import from NonNegativeInteger
      not zero? minIndex r => error "not implemented"
      n := (#r)::I
      for k in (shift(n,-1) - 1).. 0 by -1 repeat siftUp(l, r, k, n)
      for k in n-1 .. 1 by -1 repeat
         swap!(r, 0, k)
         siftUp(l, r, 0, k)
      r

    partition(l, r, i, j, k): I ==
        -- partition r[i..j] such that r.s <= r.k <= r.t
        x := qelt(r, k)
        while i <= j repeat
            t := qelt(r, i)
            while l(t, x) repeat
                i := i + 1
                t := qelt(r, i)
            s := qelt(r, j)
            while l(x, s) repeat
                j := j - 1
                s := qelt(r, j)
            if i <= j then
                qsetelt!(r, i, s)
                qsetelt!(r, j, t)
                i := i + 1
                j := j - 1
        j + 1

    QuickSort(l, r, i, j): V ==
        repeat
            n := j - i
            if (n = 1) and l(qelt(r, j), qelt(r, i)) then swap!(r, i, j)
            n < 2 => return r
            -- for the moment split at the middle item
            k := partition(l, r, i, j, i + shift(n,-1))
            if k - i < j - k then
                QuickSort(l, r, i, k - 1)
                i := k
            else
                QuickSort(l, r, k, j)
                j := k - 1

    shellSort(l, r): V ==
      m := minIndex r
      n := maxIndex r
      -- use Knuths gap sequence: 1,4,13,40,121,...
      g := 1
      while g <= (n-m) repeat g := 3*g+1
      g := g quo 3
      while g > 0 repeat
         for i in m+g..n repeat
            j := i-g
            while j >= m and l(qelt(r, j+g), qelt(r, j)) repeat
               swap!(r,j,j+g)
               j := j-g
         g := g quo 3
      r
