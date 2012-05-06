--DEPS: Integer
#include "axiom.as"

import from Boolean;
#pile

-- Not identical to Axiom code.  Added a '%', so we
-- can have multiple generators running at the same time.
RandomNumberGenerator: with
        new: () -> %;
    -- If r := randnum() then  0 <= r < size().
        randnum:  % -> Integer
           ++ randnum() is a random number between 0 and size().
    --   If r := randnum() then  0 <= r < size().
        size:     % -> Integer
          ++ size() is the base of the random number generator
        -- If r := randnum n and n <= size()  then  0 <= r < n.
        randnum:  (%, Integer) -> Integer
           ++ randnum(n) is a random number between 0 and n.
        reseed:   (%, Integer) -> ()
           ++ reseed(n) restarts the random number generator at n.
        seed : % -> Integer
           ++ seed() returns the current seed value.

    == add
        -- This random number generator passes the spectral test
        -- with flying colours. [Knuth vol2, 2nd ed, p105]
        ranbase: Integer == 2^31-1
	Rep ==> Record(x0: Integer, x1: Integer);
	import from Rep;
        new(): % == per [1231231231, 3243232987];

        randnum(r: %): Integer ==
	    (x0, x1) := explode rep r;
            t := (271828183 * x1 - 314159269 * x0) rem ranbase
            if t < 0 then t := t + ranbase
            x0:= x1
            x1:= t

        size(r: %): Integer == ranbase;
        reseed(r: %, n: Integer): () ==
            rep(r).x0 := n rem ranbase
            -- x1 := (n quo ranbase) rem ranbase
            rep(r).x1 := n quo ranbase

        seed(r: %): Integer == 
	    (x0, x1) := explode rep r;
	    x1*ranbase + x0

        -- Compute an integer in 0..n-1.
        randnum(r: %, n: Integer): Integer ==
            (n * randnum(r)) quo ranbase
