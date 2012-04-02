--DEPS: OutputForm SegmentCategory SetCategory SegmentExpansionCategory
--DEPS: List_StreamAggregate

#include "axiom.as"

import from Boolean;
import from System;
import from String;

SS(S:Type): with {
    if S has OrderedRing then expand: List % -> List S;
    if S has OrderedRing then SetCategory;
}
== add {
    if S has OrderedRing then {
      expand(ls: List %): List S == never;
   }
   if S has OrderedRing then {
       coerce(x: %): OutputForm == never;
       (a: %) = (b: %): Boolean == never;
   }
}
#if NOTES
importing 'List %' [knowing that S has OrderedRing]
... produces list containing 'hash: List % -> SingleInteger 
    	     	  	     	    [if % has Evalable % or % has SetCategory]'
.. calling symeCheckCondition('hash: % -> SingleInteger')
.. Check condition '% has Evalable %'
.. Lookup tform Evalable %
.. type infer Evalable % [no conditions applied]
#endif
