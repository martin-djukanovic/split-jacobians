/*
  Fix two elliptic curves in the Hesse pencil, with the identity element [-1:1:0];
  E1: x^3 + y^3 + z^3 + s*x*y*z = 0
  E2: x^3 + y^3 + z^3 + t*x*y*z = 0
  From the formulas in the Appendix, we have the following on E1 and E2:
  - the automorphism [-1] is given by [x : y : z] |--> [y : x : z]
  - translation by P1=[-1 : 0 : 1] is given by   [x : y : z] |--> [y : z : x]
  - translation by P2=[-w : 1 : 0] is given by   [x : y : z] |--> [w^2*x : w*y : z]
  - translation by P3=[-w^2 : 1 : 0] is given by [x : y : z] |--> [w*x : w^2*y : z]
*/

QQ:=Rationals();
R<x> := PolynomialRing(QQ);
K<w> := NumberField(1+x+x^2);
L<s,t> := FunctionField(K,2);
P8<X1,X2,X3,X4,X5,X6,X7,X8,X9> := ProjectiveSpace(L,8);

// equations defining the surface A=SegreProduct([E1,E2])
A := Scheme(P8, [
  X3^3 + X6^3 + X9^3 + s*X3*X6*X9,
  X2^3 + X5^3 + X8^3 + s*X2*X5*X8,
  X1^3 + X4^3 + X7^3 + s*X1*X4*X7,
  X7^3 + X8^3 + X9^3 + t*X7*X8*X9,
  X4^3 + X5^3 + X6^3 + t*X4*X5*X6,
  X1^3 + X2^3 + X3^3 + t*X1*X2*X3,
  X6*X8 - X5*X9,
  X3*X8 - X2*X9,
  X6*X7 - X4*X9,
  X5*X7 - X4*X8,
  X3*X7 - X1*X9,
  X2*X7 - X1*X8,
  X3*X5 - X2*X6,
  X3*X4 - X1*X6,
  X2*X4 - X1*X5
]);

/*
Hence on A we have:
- the automorphism [-1] is given by  [X1,X2,X3,X4,X5,X6,X7,X8,X9] |--> [X5,X4,X6,X2,X1,X3,X8,X7,X9]
- translation by (P1,P1) is given by [X1,X2,X3,X4,X5,X6,X7,X8,X9] |--> [X5,X6,X4,X8,X9,X7,X2,X3,X1]
- translation by (P2,P3) is given by [X1,X2,X3,X4,X5,X6,X7,X8,X9] |--> [X1,w*X2,w^2*X3,w^2*X4,X5,w*X6,w*X7,w^2*X8,X9]
- all three morphisms fix the hyperplane section X1 + X5 + X9 = 0
- A[2] consists of the points fixed by [-1] so it is the union of the schemes
  S1 := Scheme(P8, [X1-X5, X2-X4, X3-X6, X7-X8]) meet A;
  S2 := Scheme(P8, [X1+X5, X2+X4, X3+X6, X7+X8, X9]) meet A;
- over K(s,t), we find the irreducible components of A[2] to be A20, A21, A22, A23, defined below
*/

// the identity point O on A
A20 := Scheme(P8, [ X1 - X5, X2 + X5, X3, X4 + X5, X6, X7, X8, X9 ]);

// the three points of order two on E1 (embedded in A)
A21 := Scheme(P8, [ 2*X5^3 + s*X5^2*X8 + X8^3, X1 + X5, X2 - X5, X3, X4 + X5, X6, X7 + X8, X9 ]);

// the three points of order two on E2 (embedded in A)
A22 := Scheme(P8, [ 2*X5^3 + t*X5^2*X6 + X6^3, X1 + X5, X2 + X5, X3 + X6, X4 - X5, X7, X8, X9 ]);

// the remaining nine points of A[2]
A23 := Scheme(P8, [
  4*X5^3 - s*t*X5^2*X9 - s*X6^2*X9 - t*X8^2*X9 - X9^3,
  2*X5^2*X6 + s*X5^2*X9 + X8^2*X9,
  2*X5*X6^2 + s*X5*X6*X9 + X8*X9^2,
  2*X6^3 + s*X6^2*X9 + X9^3,
  2*X5^2*X8 + t*X5^2*X9 + X6^2*X9,
  2*X5*X8^2 + t*X5*X8*X9 + X6*X9^2,
  2*X8^3 + t*X8^2*X9 + X9^3,
  X6*X8 - X5*X9,
  X1 - X5,
  X2 - X5,
  X3 - X6,
  X4 - X5,
  X7 - X8
]);

// the hyperplane section on A invariant under the actions of G and [-1]
H1 := Scheme(P8, [ X1 + X5 + X9 ]);
D := H1 meet A;

/* D does not contain O, but it contains the order-2 points of E1 and E2 (embedded in A) */
not(A20 subset H1);
A21 subset H1;
A22 subset H1;
