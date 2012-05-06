#include "axiom"

CoercibleTo(S:with): Category == with {
    coerce: % -> S
      ++ coerce(a) transforms a into an element of S.
}

