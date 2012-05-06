--DEPS:  lang
#include "axiom.as"

ConvertibleTo(S:Type): Category == with {
    convert: % -> S
      ++ convert(a) transforms a into an element of S.
}