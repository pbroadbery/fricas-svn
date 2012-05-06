#include "axiom.as"

Comparable: Category == SetCategory with {
  --operations
    smaller?: (%,%) -> Boolean;
      ++ smaller?(x, y) is a strict total ordering on the elements of the set.
}