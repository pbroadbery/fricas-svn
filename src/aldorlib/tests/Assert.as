--DEPS: tests/Assertions SetCategory Ring OutputForm
--DEPS: NonNegativeInteger_OrderedAbelianMonoidSup runtime/ARCH/Local 
--DEPS: String_SetCategory 

#include "axiom"

Assert(T: with): with {
    if T has SetCategory then
      assertEquals: (T, T) -> ();
    if T has AbelianMonoid then {
      assertZero: T -> ();
      assertZero: T -> ();
    }
    assertNotNull: T -> ();
}
== add {
    import from List OutputForm;
    import from OutputForm;
    import from IO;
    import from String;

    if T has SetCategory then
      assertEquals(a: T, b: T): () == if not(a = b) then {
        print bracket [coerce "expected ", a::OutputForm, coerce " got ", b::OutputForm];
        never;
      }

    if T has AbelianMonoid then {
      assertZero(a: T): () == if zero? a then never;
      assertNotZero(a: T): () == if not zero? a then never
    }

    assertNotNull(a: T): () == never;
}