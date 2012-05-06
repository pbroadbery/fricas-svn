
HomomorphismTest(R: Ring, S: Ring): with {
    test(h: Homomorphism, r: R);
}
== add {
    test(h: Homomorphism(R, S), r: R, l: List Cross(R, R)): () == {
        for (a, b) in l repeat {
	   test(h(a) + h(b) = h(a+b))
	   test(h(a) * h(b) = h(a*b))
	}
    }
}