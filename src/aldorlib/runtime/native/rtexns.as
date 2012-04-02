--DEPS: lang init_String init_Pointer

#include "axiom.as"

-- Basic runtime functionality.  Name is required by runtime & interpreter
-- This file can pull in a full library (it doesn't because I'm lazy)
export {
--	aldorRuntimeException: String -> ();
--	aldorUnhandledException: Pointer -> ();
} to Foreign Builtin;

--aldorRuntimeException(s: String): () == exit(1$Machine);
--aldorUnhandledException(p: Pointer): () == never;