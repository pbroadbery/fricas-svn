#include "axiom.as"

import {
one: () -> XLisp;
zero: () -> XLisp;
} from Foreign Lisp;

SingleInteger: with {
	0: %;
	1: %;
} == add {
  Rep ==> XLisp;
1: % == per one();
0: % == per zero();
}