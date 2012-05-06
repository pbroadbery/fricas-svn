--DEPS: Integer
#include "axiom.as"

import from Boolean;

#pile
-- Not identical to Axiom code
RandomNumberSource(): with
    -- If r := randnum() then  0 <= r < size().
        randnum:  () -> Integer
           ++ randnum() is a random number between 0 and size().
    --   If r := randnum() then  0 <= r < size().
        size:     () -> Integer
          ++ size() is the base of the random number generator

        -- If r := randnum n and n <= size()  then  0 <= r < n.
        randnum:  Integer -> Integer
           ++ randnum(n) is a random number between 0 and n.
        reseed:   Integer -> ()
           ++ reseed(n) restarts the random number generator at n.
        seed : () -> Integer
           ++ seed() returns the current seed value.

    == add
        -- This random number generator passes the spectral test
        -- with flying colours. [Knuth vol2, 2nd ed, p105]
        local ranbase: Integer := 2^31-1
        local x0:   Integer := 1231231231
        local x1:   Integer := 3243232987

        randnum(): Integer ==
	    free x0, x1;
            t: Integer := (271828183 * x1 - 314159269 * x0) rem ranbase
            if t < 0 then t := t + ranbase
            x0:= x1
            x1:= t

        size(): Integer == ranbase
        reseed(n: Integer): () ==
	    free x0, x1;
            x0 := n rem ranbase
            -- x1 := (n quo ranbase) rem ranbase
            x1 := n quo ranbase

        seed(): Integer == x1*ranbase + x0

        -- Compute an integer in 0..n-1.
        randnum(n: Integer): Integer ==
            (n * randnum()) quo ranbase
