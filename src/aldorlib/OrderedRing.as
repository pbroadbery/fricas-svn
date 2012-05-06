#include "axiom"

import from Boolean;
import from System;
import from String;

OrderedRing: Category == Join(OrderedAbelianGroup,Ring,Monoid) with {
     positive?: % -> Boolean;
       ++ positive?(x) tests whether x is strictly greater than 0.
     negative?: % -> Boolean;
       ++ negative?(x) tests whether x is strictly less than 0.
     sign     : % -> Integer;
       ++ sign(x) is 1 if x is positive, -1 if x is negative, 0 if x equals 0.
     abs      : % -> %;
       ++ abs(x) returns the absolute value of x.
default {
     default x: %;

     positive? x: Boolean == x>0;
     negative? x: Boolean == x<0;
     sign x: Integer == {
       positive? x => 1;
       negative? x => -1;
       zero? x => 0;
       error "x satisfies neither positive?, negative? or zero?"; }
     abs x: % == {
       positive? x => x;
       negative? x => -x;
       zero? x => 0;
       error "x satisfies neither positive?, negative? or zero?"}

}
}
