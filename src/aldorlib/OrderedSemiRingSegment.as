--DEPS: OrderedAbelianMonoidSup SemiRing init_Generator
#include "axiom.as"
#pile
import from System
import from String

-- This can be used in cases where a Segment NNI is needed.  The
-- problem is that UniversalSegment represents its increment by an
-- integer which is then coerced into the base type on demand.
-- However, only a Ring (or better) exports a coerce: I -> %.
-- Consequently we can't use it for NNI.  Instead we have this type,
-- which works for anything with '1', '+' and '<'.  The 'sup' part isn't
-- used, although there is an argument we should instead insist on a total order.

OrderedSemiRingSegment(T: Join(OrderedAbelianMonoidSup, SemiRing)): Exports == Implementation where
    Exports ==> with
        generator: % -> Generator T
	..: (T, T) -> %
	..: T -> %
    Implementation ==> add
        Rep == Record(bounded: Boolean, lo: T, hi: T);
	import from Rep

	-- TODO: The error here assumes that 1 > 0.  Almost certainly true, should prove it though
	(lo: T) .. (hi: T): % == 
	    hi < lo => error "hi < lo in OrderedSemiRingSegment.  You probably didn't want this."
	    per [true, lo, hi]

	(lo: T) .. : % == 
	    per [false, lo, 0]
	

	generator(t: %): Generator T == 
            low := rep(t).lo	    
	    generate 
	        current := low
	        while underLimit?(current, t) repeat 
	            yield current
	            current := current + 1
	
        local bounded?(t: %): Boolean == rep(t).bounded
	local underLimit?(c: T, t: %): Boolean == 
	    not bounded? t => true
	    c <= rep(t).hi