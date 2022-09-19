/* Here we verify by direct computation that if E1 and E2 are glued along the 3-torsion via an isomorphism E1[3]-->E2[3] that is induced by a 2-isogeny,
   then the abelian surface so obtained is isomorphic to A = E1 x E2. We denote by G the graph of the isomorphism E1[3]-->E2[3]. */
R<x> := PolynomialRing(QQ);
K<w> := ext<QQ|1+x+x^2>;
K<t> := FunctionField(K);
R<x> := PolynomialRing(K);
P2<X,Y,Z> := ProjectiveSpace(K,2);
P8<X1,X2,X3,X4,X5,X6,X7,X8,X9> := ProjectiveSpace(K,8);
P3<x1,x2,x3,x4> := ProjectiveSpace(K,3);

// a rational parametrization of the curve 3a^2b^2 + a^3 + b^3 - 3ab + 2 = 0:
a := -(1+2*t^3)/(3*t^2);
b := (1-4*t^3)/(3*t);

// the two 2-isogenous elements of the Hesse pencil (see Example 5.2)
E1 := Curve(P2, X^3 + Y^3 + Z^3 + 3*a*X*Y*Z);
E2 := Curve(P2, X^3 + Y^3 + Z^3 + 3*b*X*Y*Z);

// the reducible divisor on E1 x E2 that is fixed by translation by elements of G and by [-1], carved by the hyperplane X1 + X5 + X9 = 0
D := Scheme(P8, [
	X3^3 + X6^3 + X9^3 + 3*a*X3*X6*X9,
	X2^3 + X5^3 + X8^3 + 3*a*X2*X5*X8,
	X1^3 + X4^3 + X7^3 + 3*a*X1*X4*X7,
	X7^3 + X8^3 + X9^3 + 3*b*X7*X8*X9,
	X4^3 + X5^3 + X6^3 + 3*b*X4*X5*X6,
	X1^3 + X2^3 + X3^3 + 3*b*X1*X2*X3,
	X6*X8 - X5*X9,
	X3*X8 - X2*X9,
	X6*X7 - X4*X9,
	X5*X7 - X4*X8,
	X3*X7 - X1*X9,
	X2*X7 - X1*X8,
	X3*X5 - X2*X6,
	X3*X4 - X1*X6,
	X2*X4 - X1*X5,
	X1 + X5 + X9
]);

// the two irreducible components of D
D1 := Scheme(P8,[
	t*X4*X7^2 + t*X5*X8^2 + (-4*t^3 + 1)*X4*X8*X9 + t*X6*X9^2,
	t*X7^3 + t*X8^3 + (-4*t^3 + 1)*X7*X8*X9 + t*X9^3,
	t*X4*X7*X8 - t*X2*X8^2 + t*X7^2*X9 + (-4*t^3 + 1)*X5*X8*X9 - t*X3*X9^2 + (-4*t^3 + 1)*X8*X9^2,
	4*t^3*X2^2 - t*X6^2 - 2*t^2*X7^2 - 2*t*X5*X8 + 4*t^2*X3*X9 + X4*X9 + t*(8*t^3 - 3)*X8*X9,
	t*X2*X3 - t*X4*X6 + X4*X7 - X2*X8 - 4*t^2*X5*X9 - 2*t^2*X9^2,
	t*X3^2 + 2*t^2*X5*X6 - X2*X9 + t*X7*X9,
	2*t^2*X2*X4 - t*X4*X6 + X4*X7 - t*X7*X8 - 2*t^2*X5*X9 - 2*t^2*X9^2,
	2*t^2*X4^2 + t*X5*X6 + X4*X8 - t*X8^2 + 2*t*X6*X9 + 4*t^3*X7*X9,
	2*t^2*X2*X5 - t*X5*X6 + X4*X8 - t*X8^2 + 2*t^2*X2*X9,
	2*t^2*X3*X5 - t*X6^2 + 2*t^2*X3*X9 + X4*X9 - t*X8*X9,
	4*t^3*X4*X5 - t*X6^2 + 2*t^2*X7^2 + 2*t*X5*X8 + X4*X9 + t*X8*X9,
	2*t^2*X5^2 + t*X4*X6 - X4*X7 + t*X7*X8 + 4*t^2*X5*X9 + 2*t^2*X9^2,
	2*t^2*X2*X6 - t*X6^2 + 2*t^2*X3*X9 + X4*X9 - t*X8*X9,
	X3*X6 - 2*t*X4*X6 + X4*X7 - X2*X8 - 4*t^2*X5*X9 - 4*t^2*X9^2,
	X3*X4 + X5*X6 + X6*X9,
	X2*X7 + X5*X8 + X8*X9,
	X3*X7 + X5*X9 + X9^2,
	X5*X7 - X4*X8,
	X3*X8 - X2*X9,
	X6*X7 - X4*X9,
	X6*X8 - X5*X9,
	X1 + X5 + X9
]);
D2 := Scheme(P8,[
	-(4*t^3 - 1)*t*X2*X8*X9 + 2*t^4*X3*X6*X9 + (4*t^3 - 1)*t^2*X4*X6*X9 + (t^3 - 1)*X5*X9^2 - (4*t^3 - 1)*t^2*X7*X8*X9 - t^3*X8^3 + (2*t^3 - 1)*X9^3 + t*X2*X5*X8,
	t*X2*X8^2 + t^2*X7*X8^2 + (2*t^3 - 1)*X5*X8*X9 + t*X3*X9^2 + t^2*X4*X9^2 + (2*t^3 - 1)*X8*X9^2, 
	t*X2^2 + 2*t^3*X2*X6 + t^2*X6^2 - t^2*X5*X8 - X3*X9 - 2*t^2*X8*X9,
	t*X3^2 - X2*X5 - 2*t^2*X5*X6 + t^2*X8^2 + 2*t^3*X2*X9 - t^2*X6*X9,
	X2*X4 + t*X3*X6 + 2*t^2*X4*X6 - t*X2*X8 - 2*t^2*X7*X8 + X5*X9 + X9^2, 
	X5^2 - t*X3*X6 - 2*t^2*X4*X6 + t*X2*X8 + 2*t^2*X7*X8 - X9^2,
	t^2*X2*X3 - t^2*X4*X6 + t*X2*X8 + t^2*X7*X8 - X5*X9 - X9^2, 
	t*X4^2 + t*X2*X5 - 2*t^3*X8^2 - 4*t^4*X2*X9 - X6*X9 - 2*t^3*X6*X9 - 2*t^2*X7*X9,
	X4*X5 + 2*t^2*X2*X6 + t*X6^2 + t*X5*X8 + X4*X9, 
	X5*X7 + t*X8^2 + 2*t^2*X2*X9 + t*X6*X9 + X7*X9, 
	X4*X8 + t*X8^2 + 2*t^2*X2*X9 + t*X6*X9 + X7*X9,
	t*X7^2 - X5*X8 + t*X3*X9 + 2*t^2*X4*X9,
	t*X4*X7 + t*X2*X8 + 2*t^2*X7*X8 - X9^2,
	X3*X4 + X5*X6 + X6*X9, 
	X2*X7 + X5*X8 + X8*X9,
	X3*X7 + X5*X9 + X9^2,
	X3*X8 - X2*X9,
	X3*X5 - X2*X6,
	X6*X7 - X4*X9,
	X6*X8 - X5*X9,
	X1 + X5 + X9
]);

Union(D1,D2) eq D and IsIrreducible(D1) and IsIrreducible(D2);
P := P8![-2*t, 1, 1, -2*t^2, t, t, -2*t^2, t, t]; // one of 9 pts of the kernel of the isogeny A -> A/G
P in D1 meet D2;

F1 := Curve(P2,[
	(t - 1)^2*(4*t^2 - 2*t + 1)*(16*t^7 - 4*t^6 + 48*t^5 + 16*t^4 + 2*t^3 + 6*t^2 - 5*t + 2)*(2*t + 1)^4*X^2*Y
	- 2*(t - 1)^4*(4*t^2 - 2*t + 1)*(2*t^3 + 6*t^2 + 1)*(2*t + 1)^6*X^2*Z
	- 108*(t - 1)*t^4*(16*t^4 + 26*t^3 - 21*t^2 + 8*t - 2)*(2*t + 1)*Y^2*Z
	+ 36*(t - 1)^3*t^4*(4*t - 1)*(8*t^2 - t + 2)*Y^3
	+ 108*t^4*(8*t^4 + 10*t^3 + 12*t^2 - 5*t + 2)*(2*t + 1)^2*Y*Z^2
	- 72*(t - 1)^2*t^4*(2*t + 1)^4*Z^3
]);
F2 := Curve(P2,[
	(2*t + 1)^2*(t^2 + t + 1)*(32*t^7 + 40*t^6 + 24*t^5 - 4*t^4 + 16*t^3 - 24*t^2 - t - 2)*(t - 1)^4*X^2*Y
	- 2*(2*t + 1)^4*(t^2 + t + 1)*(4*t^3 + 6*t - 1)*(t - 1)^6*X^2*Z
	- 54*t^5*(2*t + 1)*(8*t^4 + 16*t^3 + 21*t^2 + 13*t - 4)*(t - 1)*Y^2*Z
	+ 9*t^5*(t + 2)*(2*t + 1)^3*(4*t^2 + t + 4)*Y^3
	+ 108*t^5*(8*t^4 + 10*t^3 + 12*t^2 - 5*t + 2)*(t - 1)^2*Y*Z^2
	- 72*t^5*(2*t + 1)^2*(t - 1)^4*Z^3
]);

// the isogeny A -> A/G, followed by a projection to P2, restricted to D1 (resp. D2); see models-of-C/curve_C_in_P3.m
f := map<D1->F1|[
	2*((w*X1 + w^2*X5 + X9)^3 + (w^2*X1 + w*X5 + X9)^3),
	2*((X3 + X4 + X8)^3 - (X2 + X6 + X7)^3),
	(w*X3 + w^2*X4 + X8)^3 - (w^2*X2 + w*X6 + X7)^3 + (w^2*X3 + w*X4 + X8)^3 - (w*X2 + w^2*X6 + X7)^3
]>;
g := map<D2->F2|[
	2*((w*X1 + w^2*X5 + X9)^3 + (w^2*X1 + w*X5 + X9)^3),
	2*((X3 + X4 + X8)^3 - (X2 + X6 + X7)^3),
	(w*X3 + w^2*X4 + X8)^3 - (w^2*X2 + w*X6 + X7)^3 + (w^2*X3 + w*X4 + X8)^3 - (w*X2 + w^2*X6 + X7)^3
]>;

E1 := EllipticCurve(E1, P2![-1,1,0]);
E2 := EllipticCurve(E2, P2![-1,1,0]);
F1 := EllipticCurve(Curve(F1), f(P));
F2 := EllipticCurve(Curve(F2), g(P));
IsIsomorphic(E1,F1) and IsIsomorphic(E2,F2);
