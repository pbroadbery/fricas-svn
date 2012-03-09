#include "axiom.as"

BasicTypeAxioms(T: BasicType): with == add {
  axioms: () -> List Axiom;   
}
== add {
   axioms(): List Axiom == {
   	 import from StreamPackage;
   	 [axiom("Reflexive", (a: %): Boolean +-> a=a, values T),
    	  axiom("Equality", (a: %, b: %): Boolean +-> a=b and not a ~= b, allPairs(T, values T));
   	  axiom("Symmetric", (a: %, b: %): Boolean +-> a=a, values T)];
   }
}
