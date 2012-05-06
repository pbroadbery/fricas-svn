--DEPS:  String OneDimensionalArrayAggregate
#include "axiom.as"

import from Boolean;

extend String: OneDimensionalArrayAggregate Character with {

} == add {
  empty(): % == never;
  elt(x: %, n: Integer): Character == never;
  setelt(x: %, n: Integer, c: Character): Character == never;
}
