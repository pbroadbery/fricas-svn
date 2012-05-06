--DEPS: ExtensibleLinearAggregate List_StreamAggregate
#include "axiom.as"

#pile

extend List(S: Type): ExtensibleLinearAggregate S with == 
 add
   
   new(n: NonNegativeInteger, e: S): % == never
   concatList(l: %): % == never
   map(f: (S, S) -> S, l1: %, l2: %): % == never
   elt(l: %, s: UniversalSegment(Integer)): % == never
   delete!(l: %, n: Integer): % == never
   delete!(l: %, s: UniversalSegment(Integer)): % == never
   remove!(f: S -> Boolean, l: %): % == never
   insert!(e: S, l: %, n: Integer): % == never
   insert!(l1: %, l2: %, n: Integer): % == never
   merge!(f: (S, S) -> Boolean, l1: %, l2: %): % == never
   select!(f: S -> Boolean, l: %): % == never
   
   if S has SetCategory then
     removeDuplicates!(l: %): % == never