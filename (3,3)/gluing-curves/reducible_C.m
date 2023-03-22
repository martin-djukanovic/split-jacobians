/* Here we verify by direct computation that if E1 and E2 are glued along the 3-torsion via an isomorphism E1[3]-->E2[3] that is induced by a 2-isogeny,
   then the abelian surface so obtained is isomorphic to A = E1 x E2. We denote by G the graph of the isomorphism E1[3]-->E2[3]. */
QQ:=Rationals();
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

// T1=[t,t,1] generates the kernel of the isogeny f:E1->E2 and T2=[1,1,-2*t] generates the kernel of the dual f`:E2->E1.

// the reducible divisor D=D1+D2 on E1 x E2 that is fixed by translation by elements of G and by [-1], carved by the hyperplane X1 + X5 + X9 = 0
D := Curve(P8, [
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

// this is the translation by (T1,T2) of the divisor consisting of points (P,f(P)) with P in E1
D1 := Curve(P8,[
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

// this is the translation by (T1,T2) of the divisor consisting of points (-f`(Q),Q) with Q in E2
D2 := Curve(P8,[
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
P:=P8![t, t, -2*t^2, t, t, -2*t^2, 1, 1, -2*t];		// this is the point (T1,T2)
P in D1 meet D2; 	 // the intersection of D1 and D2 is G + (T1,T2)


// the isogeny A -> A/G
g := map<P8->P8|[
        2*(X1+X5+X9)^3,
	2*((w*X1 + w^2*X5 + X9)^3 + (w^2*X1 + w*X5 + X9)^3),   
        3/(w-w^2)*((w*X1 + w^2*X5 + X9)^3 - (w^2*X1 + w*X5 + X9)^3),
        2*((X3 + X4 + X8)^3 + (X2 + X6 + X7)^3),     
        2*((X3 + X4 + X8)^3 - (X2 + X6 + X7)^3),
        (w*X3 + w^2*X4 + X8)^3 + (w^2*X3 + w*X4 + X8)^3 + (w^2*X2 + w*X6 + X7)^3 + (w*X2 + w^2*X6 + X7)^3,
        (w*X3 + w^2*X4 + X8)^3 + (w^2*X3 + w*X4 + X8)^3 - (w^2*X2 + w*X6 + X7)^3 - (w*X2 + w^2*X6 + X7)^3,
        3/(w-w^2)*((w*X3 + w^2*X4 + X8)^3 - (w^2*X3 + w*X4 + X8)^3 + (w*X2 + w^2*X6 + X7)^3 - (w^2*X2 + w*X6 + X7)^3),
        3/(w-w^2)*((w*X3 + w^2*X4 + X8)^3 - (w^2*X3 + w*X4 + X8)^3 - (w*X2 + w^2*X6 + X7)^3 + (w^2*X2 + w*X6 + X7)^3)
]>;
/* g is defined by linear combinations of 
   (X1 + X5 + X9)^3, (w*X1 + w^2*X5 + X9)^3, (w^2*X1 + w*X5 + X9)^3,
   (X3 + X4 + X8)^3, (w*X3 + w^2*X4 + X8)^3, (w^2*X3 + w*X4 + X8)^3,
   (X2 + X6 + X7)^3, (w*X2 + w^2*X6 + X7)^3,  (w^2*X2 + w*X6 + X7)^3
   The scalars can be chosen so that it is defined over QQ (or Fp in characteristic p), e.g. as above.
*/
F1:=g(D1);
F2:=g(D2);
Degree(F1 meet F2) eq 1;


/************* below we verify that D1 and D2 are as claimed *************/
// translation by (T1,T2)
tr:=map<P8->P8|[
    2*t^3*X2*X8 + t^2*X3*X7 - t*X4*X6 - 2*t^2*X5^2,
    2*t^3*X1*X7 + t^2*X3*X8 - 2*t^2*X4^2 - t*X5*X6,
    4*t^4*X2*X7 - t^2*X3*X9 - 4*t^3*X4*X5 + t*X6^2,
    -t*X1*X3 - 2*t^2*X2^2 + 2*t^3*X5*X8 + t^2*X6*X7,
    -2*t^2*X1^2 - t*X2*X3 + 2*t^3*X4*X7 + t^2*X6*X8,
    -4*t^3*X1*X2 + t*X3^2 + 4*t^4*X5*X7 - t^2*X6*X9,
    2*t*X2*X5 + X3*X4 - t^2*X7*X9 - 2*t^3*X8^2,
    2*t*X1*X4 + X3*X5 - 2*t^3*X7^2 - t^2*X8*X9,
    4*t^2*X2*X4 - X3*X6 - 4*t^4*X7*X8 + t^2*X9^2
]>;

// the map (P,Q)|-->(P,f(P))
PfP:=map<P8->P8|[
  X2^2*(t^2*X1^2 - t^2*X1*X4 - 2*t^2*X4^2 + 2*t^3*X1*X7 - X4*X7 + t*X7^2), 
  -X2*(2*t^2*X1*X2*X4 + t^2*X2*X4^2 - t^2*X4^2*X5 + X2*X4*X7 - 2*t^3*X4*X5*X7 - t*X5*X7^2), 
  -t*X2*X7*((-X1)*X2 - 2*X2*X4 - X4*X5 + t*X2*X7 + t*X5*X7 + 2*t^2*X7*X8), 
  X2*(t^2*X1*X2*X4 - t^2*X2*X4^2 - 2*t^2*X4^2*X5 + 2*t^3*X2*X4*X7 - X4*X5*X7 + t*X5*X7^2), 
  -2*t^2*X2^2*X4^2 - t^2*X2*X4^2*X5 + t^2*X4^2*X5^2 - X2*X4*X5*X7 + 2*t^3*X4*X5^2*X7 + t*X5^2*X7^2,
  -t*X7*(-X2^2*X4 - 2*X2*X4*X5 - X4*X5^2 + t*X2*X5*X7 + t*X5^2*X7 + 2*t^2*X5*X7*X8),
  X2*X7*(t^2*X1*X2 - t^2*X2*X4 - 2*t^2*X4*X5 + 2*t^3*X2*X7 - X5*X7 + t*X7*X8), 
  X7*(-2*t^2*X2^2*X4 - t^2*X2*X4*X5 + t^2*X4*X5^2 - X2*X5*X7 + 2*t^3*X5^2*X7 + t*X5*X7*X8), 
  -t*X7^2*(X2 + X5 + t*X8)*(-X2 - X5 + 2*t*X8)
]>;

// the map (P,Q)|-->(-f`(Q),Q)
fQQ:=map<P8->P8|[
  X4*(t*X4^2*X5 + 2*t*X4*X5^2 + t*X5^3 + X4^2*X6 + X4*X5*X6 + 2*t^2*X4*X6^2 + t*X6^3), 
  X5*(t*X4^2*X5 + 2*t*X4*X5^2 + t*X5^3 + X4^2*X6 + X4*X5*X6 + 2*t^2*X4*X6^2 + t*X6^3), 
  X6*(t*X4^2*X5 + 2*t*X4*X5^2 + t*X5^3 + X4^2*X6 + X4*X5*X6 + 2*t^2*X4*X6^2 + t*X6^3), 
  X4*(t*X4^3 + 2*t*X4^2*X5 + t*X4*X5^2 + X4*X5*X6 + X5^2*X6 + 2*t^2*X5*X6^2 + t*X6^3), 
  X5*(t*X4^3 + 2*t*X4^2*X5 + t*X4*X5^2 + X4*X5*X6 + X5^2*X6 + 2*t^2*X5*X6^2 + t*X6^3), 
  X6*(t*X4^3 + 2*t*X4^2*X5 + t*X4*X5^2 + X4*X5*X6 + X5^2*X6 + 2*t^2*X5*X6^2 + t*X6^3), 
  X4*(2*t*X4 + 2*t*X5 - X6)*X6*(t*X4 + t*X5 + X6), X5*(2*t*X4 + 2*t*X5 - X6)*X6*
  (t*X4 + t*X5 + X6), (2*t*X4 + 2*t*X5 - X6)*X6^2*(t*X4 + t*X5 + X6)
]>;

// the curves E1 and E2 as divisors on E1 x E2
EE1:=Curve(P8,[X1+X2, X4+X5, X7+X8, X3, X6, X9, X2^3 + X5^3 + X8^3 + 3*a*X2*X5*X8 ]);
EE2:=Curve(P8,[X1+X4, X2+X5, X3+X6, X7, X8, X9, X4^3 + X5^3 + X6^3 + 3*b*X4*X5*X6 ]);
PfP(EE1) eq tr(D1);
fQQ(EE2) eq tr(D2);


// the divisors defining the polarizations are both isomorphic to E1 + E2:
E1 := EllipticCurve(E1, P2![-1,1,0]);
E2 := EllipticCurve(E2, P2![-1,1,0]);
D1 := EllipticCurve(D1, P);
D2 := EllipticCurve(D2, P);
F1 := EllipticCurve(F1, g(P));
F2 := EllipticCurve(F2, g(P));
IsIsomorphic(E1,F1) and IsIsomorphic(E2,F2) and IsIsomorphic(E1,D1) and IsIsomorphic(E2,D2);
