
Field: Category == Join(EuclideanDomain,UniqueFactorizationDomain,
  DivisionRing, canonicalUnitNormal, canonicalsClosed) with {
    --operations
      /: (%,%) -> %;
        ++ x/y divides the element x by the element y.
        ++ Error: if y is 0.
    default {
      --declarations
      default x,y: %;
      default n: Integer;
      -- definitions
      UCA ==> Record(unit:%,canonical:%,associate:%);
      unitNormal(x) ==
          if zero? x then [1$%,0$%,1$%]$UCA else [x,1$%,inv(x)]$UCA;
      unitCanonical(x) == if zero? x then x else 1;
      associates?(x,y) == if zero? x then zero? y else not(zero? y);
      inv x ==((u:=recip x) case "failed" => error "not invertible"; u);
      x exquo y == (y=0 => "failed"; x / y);
      gcd(x,y) == 1;
      euclideanSize(x) == 0;
      prime? x == false;
      squareFree x == x::Factored(%);
      factor x == x::Factored(%);
      x / y == (zero? y => error "catdef: division by zero"; x * inv(y));
      divide(x,y) == [x / y,0];
}
}