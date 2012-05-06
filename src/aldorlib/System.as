#include "axiom"

import from Boolean;

System: with {
	error: String -> Exit;
}
== add {
   error(s: String): Exit == never;
}
