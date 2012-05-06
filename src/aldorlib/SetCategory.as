--DEPS:  BasicType CoercibleTo init_OutputForm String init_SingleInteger

#include "axiom"

SetCategory: Category == Join(BasicType,CoercibleTo OutputForm) with {
    --operations
      hash: % -> SingleInteger;  ++ hash(s) calculates a hash code for s.
      latex: % -> String;       ++ latex(s) returns a LaTeX-printable output
                               ++ representation of s.
  default {
      hash(s : %):  SingleInteger == 0$SingleInteger;
      latex(s : %): String       == "\mbox{\bf Unimplemented}"
  }
}