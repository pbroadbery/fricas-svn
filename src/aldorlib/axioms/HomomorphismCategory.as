--DEPS: axioms/Axiom axioms/Stream
#include "axiom.as"

HomomorphismCategory(R1: Ring, R2: Ring): Category == with {
   apply: (%, R1) -> R2;
   kernel?: (%, R1) -> Boolean;
} 
