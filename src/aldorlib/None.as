--DEPS: OutputForm String_SetCategory
#include "axiom.as"
#pile
import from String

None: SetCategory with
== add
    coerce(none:%):OutputForm == "NONE" :: OutputForm

    (x:%) = (y:%): Boolean == EQ(x,y)$ListLisp(%)
