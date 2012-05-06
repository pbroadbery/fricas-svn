#include "axiom"

extend String: with {
       string: Literal -> String;
}
== add {
   string(x: Literal): String == x pretend String;
}
