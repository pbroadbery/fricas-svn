--DEPS: Character_Base OrderedFinite
#include "axiom.as"
#pile

extend Character: OrderedFinite with _
== add
 coerce(a: %): OutputForm == never
 size(): NonNegativeInteger == never
 index(p: PositiveInteger): % == never
 lookup(c: %): PositiveInteger == never

