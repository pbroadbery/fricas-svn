--DEPS: lang

#include "axiom.as"

export {
	aldorRuntimeException: String -> ();
	aldorUnhandledException: Pointer -> ();
} to Foreign Builtin;

import {
       exit: SInt$Machine -> Exit;
} from Foreign Builtin "<stdlib.h>";

aldorRuntimeException(String s): () == exit(1);
aldorUnhandledException(p: Pointer): () == never;