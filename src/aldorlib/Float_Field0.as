--DEPS: Float_SetCategory Field0
#include "axiom.as"

#pile
extend Float: Field0 with 
== add 
 =(a: %, b: %): Boolean == never
 coerce(a: %): OutputForm == never
 +(a: %, b: %): % == never
 0: % == never
 -(a: %): % == never
 (*)(a: %, b: %): % == never
 1: % == never
 characteristic(): NonNegativeInteger == never
 (*)(a: %, b: Fraction(Integer)): % == never
 inv(a: %): % == never
 (/)(a: %, b: %): % == never


