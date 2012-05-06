#include "axiom"

extend OutputForm: with {
       bracket: % -> %;
       commaSeparate: List % -> %;
} == add {
  [x: %]: % == never;
  commaSeparate(l: List %): % == never;
}
