/* These are examples of curves E1: x^3 + y^3 + z^3 + 3axyz = 0 and E2: x^3 + y^3 + z^3 + 3bxyz = 0,
   with identity element O=[-1:1:0], glued along the graph of the isomorphism E1[3] -> E2[3] that is given by
   [-1:0:1] -> [-1:0:1] [-w:1:0] -> [-w^2:1:0]. A concrete affine plane model is given for C, not just the isomorphism class.
*/

K:=Rationals();
R<x> := PolynomialRing(K);
K<w> := ext<K| 1+x+x^2>;
R<x> := PolynomialRing(K);
P8<X1,X2,X3,X4,X5,X6,X7,X8,X9> := ProjectiveSpace(K,8);
P2<X,Y,Z> := ProjectiveSpace(K,2);
D := func<a,b | Scheme(P8, [
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
])>;


/* Example 1: The Fermat curve x^3 + y^3 + z^3 = 0 glued with itself gives the Jacobian of -6y^2 = (x^3-2)(2x^3-1) */
f:=map<P8->P2 | [
	(w*X1 + w^2*X5 + X9)^3 - (w^2*X1 + w*X5 + X9)^3 + (w*X3 + w^2*X4 + X8)^3 - (w^2*X2 + w*X6 + X7)^3 + (w*X2 + w^2*X6 + X7)^3 - (w^2*X3 + w*X4 + X8)^3,
	(X3 + X4 + X8)^3 + (X2 + X6 + X7)^3,
	(X3 + X4 + X8)^3 - (X2 + X6 + X7)^3
]>;
C:=f(D(0,0));
g:=map<P2->P2 | [ ((2*w + 1)*X - 9*Z)*((2*w + 1)*X + 9*Z)^2, 2^3*3^5*Y*Z^2, ((2*w + 1)*X + 9*Z)^3]>;
g(C);


/* Example 2: The curve x^3 + y^3 + z^3 + 6xyz = 0, which is isomorphic to the Fermat curve, gives the same result. */
f:=map<P8->P2 | [
	(X3 + X4 + X8)^3 - (X2 + X6 + X7)^3,
	(X3 + X4 + X8)^3 + (X2 + X6 + X7)^3,
	7*(w*X1 + w^2*X5 + X9)^3 - 7*(w^2*X1 + w*X5 + X9)^3 + (w*X3 + w^2*X4 + X8)^3 - (w^2*X2 + w*X6 + X7)^3 + (w*X2 + w^2*X6 + X7)^3 - (w^2*X3 + w*X4 + X8)^3
]>;
C:=f(D(2,2));
g:=map<P2->P2 | [ X*Z^2, Y*(X^2-Z^2), Z^3 ]>;
h:=map<P2->P2 | [(Z - X*(1 + 2*w))*(Z + X*(1 + 2*w))^2, 6*Y*Z^2, (Z + X*(1 + 2*w))^3 ]>;
h(g(C));


/* Example 3: Gluing x^3 + y^3 + z^3 + 6xyz = 0 with the Fermat curve gives the Jacobian of -6y^2=(x^3 + 6x^2 + 12x + 10)(10x^3 + 36x^2 + 60x + 25)
   This already becomes quite tedious.
*/
P3<x1,x2,x3,x4>:=ProjectiveSpace(K,3);
f:=map<P8->P3 | [
	(X3 + X4 + X8)^3 + (X2 + X6 + X7)^3,
	(X3 + X4 + X8)^3 - (X2 + X6 + X7)^3,
	(w*X3 + w^2*X4 + X8)^3 - (w^2*X2 + w*X6 + X7)^3,
	(w^2*X3 + w*X4 + X8)^3 - (w*X2 + w^2*X6 + X7)^3
]>;
C:=f(D(0,2)); //f(D(2,0)) is obtained by swapping w and w^2.
g1:=map<P3->P2 | [ 247*x3 + (72*w + 275)*x4, x1, -11*x2 + (23 + 17*w)*x3 + (6 - 17*w)*x4 ]>;
g2:=map<P2->P2 | [ (29*w + 4)^2*X*Z, (29*w + 4)^6*(57838*w + 15851)/85107555*Y*(21*X + (4*w + 29)*Z), 247*Z^2]>;
g3:=map<P2->P2 | [ 5*((16 - 100*w)*X + 741*Z)*((-20 + 125*w)*X + 5187*Z)^2, 34875*(7687 + 2900*w)*Y*Z^2, ((-20 + 125*w)*X + 5187*Z)^3 ]>;
g3(g2(g1(C)));
