--DEPS: OutputForm SegmentCategory SetCategory SegmentExpansionCategory
--DEPS: List_StreamAggregate

#include "axiom.as"

import from Boolean;
import from System;
import from String;

TT(S:Type): with {
    if S has OrderedRing then expand: List List S -> List S;
}
== add {
    if S has OrderedRing then {
      expand(ls: List List S): List S == never;
   }
}
#if NOTES
importing 'List S' [knowing that S has OrderedRing]
... produces list containing 'hash: List S -> SingleInteger 
    	     	  	     	    [if S has Evalable S]'
.. calling symeCheckCondition('hash: % -> SingleInteger')
.. Check condition 'List S has Evalable S'
.. Lookup tform Evalable S
.. type infer Evalable % [no conditions applied]
#endif
