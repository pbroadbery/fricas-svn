--DEPS: OrderedAbelianMonoidSup SemiRing init_Generator
#include "axiom.as"
#pile
import from System
import from String

-- This can be used in cases where a Segment NNI is needed.
-- The problem is that UniversalSegment represents its increment by
-- an integer coerced into the base type.  However, only a Ring (or better)
-- exports a coerce: I -> %.  Consequently we can't use it for NNI.
-- Instead we have this type, which works for 
OrderedSemiRingSegment(T: Join(OrderedAbelianMonoidSup, SemiRing)): Exports == Implementation where
    Exports ==> with
        generator: % -> Generator T
	..: (T, T) -> %
    Implementation ==> add
        Rep == Record(lo: T, hi: T);
	import from Rep

	(lo: T) .. (hi: T): % == 
	    hi < lo => error "hi < lo in universal segment.  You probably didn't want this."
	    per [lo, hi]
	generator(t: %): Generator T == generate 
	    lo := rep(x).lo	    
	    hi := rep(x).hi
	    current := lo
	    while current <= hi repeat 
	        yield current
		current := current + 1
