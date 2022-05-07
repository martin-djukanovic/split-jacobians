/* These are examples of curves E1: x^3 + y^3 + z^3 + 3axyz = 0 and E2: x^3 + y^3 + z^3 + 3bxyz = 0,
   with identity element O=[-1:1:0], glued along the graph of the isomorphism E1[3] -> E2[3] that is given by
   [-1:0:1] -> [-1:0:1] [-w:1:0] -> [-w^2:1:0]. A concrete affine plane model is given for C, not just the isomorphism class.
*/

K:=Rationals();
R<x> := PolynomialRing(K);
K<w> := ext<K | 1+x+x^2>;
R<x> := PolynomialRing(K);
P8<X1,X2,X3,X4,X5,X6,X7,X8,X9> := ProjectiveSpace(K,8);
P3<x1,x2,x3,x4> := ProjectiveSpace(K,3);
P2<X,Y,Z> := ProjectiveSpace(K,2);

// This model is derived in curve_C.m
C := func<a,b | Scheme(P3, [
   (2 - 9*a - 9*b + 9*a^2 + 9*b^2 + 24*a*b + a^3 + b^3 - 9*a^3*b - 9*a*b^3 - 24*a^2*b^2 + 9*a^3*b^2 + 9*a^2*b^3)*x2^3
   + (16 + 63*a + 63*b - 36*a^2 - 36*b^2 + 408*a*b - 19*a^3 - 19*b^3 + 189*a^2*b + 189*a*b^2 + 36*a^3*b + 36*a*b^3 + 24*a^2*b^2 - 9*a^3*b^2 - 9*a^2*b^3)*x3^3 
   + 3*(4 - 27*a - 27*b + 36*a^2 + 36*b^2 + 120*a*b - 7*a^3 - 7*b^3 - 72*a^2*b - 72*a*b^2 + 18*a^3*b + 18*a*b^3 + 24*a^2*b^2 - 9*a^3*b^2 - 9*a^2*b^3)*x2^2*x3 
   + 3*(-10 + 9*a + 9*b - 27*a^2 - 27*b^2 + 222*a*b + 13*a^3 + 13*b^3 + 9*a^2*b + 9*a*b^2 - 24*a^2*b^2 - 27*a^3*b - 27*a*b^3 + 9*a^3*b^2 + 9*a^2*b^3)*x3^2*x2
   + 9*(-2 - a - b + 3*a^2 + 3*b^2 - 2*a*b + 3*a^3 + 3*b^3 - a^2*b - a*b^2 - 8*a^2*b^2 + 3*a^3*b + 3*a*b^3 - a^2*b^3 - a^3*b^2)*x2*x4^2
   + 9*(1 + a)*(1 + b)*(a + b - a^2 - b^2 + 6*a*b + a^2*b + a*b^2)*x4^2*x3
   + 9*(b - a)*(1 + a)^2*(1 + b)^2*x4^3
   + 9*(b - a)*(1 - 2*a - 2*b + 3*a^2 + 3*b^2 + 9*a*b - 4*a^2*b - 4*a*b^2 - a^2*b^2)*x2^2*x4
   + 9*(b - a)*(1 + a)*(1 + b)*(7 + 3*a + 3*b - a*b)*x3^2*x4
   + 18*(b - a)*(5 + 5*a  + 5*b - 3*a^2 - 3*b^2 + 12*a*b + a^2*b + a*b^2 + a^2*b^2)*x2*x3*x4,
   (2 - 3*a*b + a^3 + b^3 + 3*a^2*b^2)*x1^2
   + 3*(1 - a*b)*x2^2 + 3*(1 + a)*(1 + b)*x4^2
   + 3*(7 + 3*a + 3*b - a*b)*x3^2
   + 9*(b - a)*x2*x4
   + 3*(10 - 3*a - 3*b + 2*a*b)*x2*x3
])>;

/* Example 1: The Fermat curve x^3 + y^3 + z^3 = 0 glued with itself gives the Jacobian of
   C: -6y^2 = (x^3-2)(2x^3-1)
*/
g := map<P3 -> P2 | [x4, x1, -x2+x3+x4]>;
h := map<P2 -> P2 | [ (2*X-Z)*Z, (2*X-Z)*Y, Z^2 ]>;
h(g(C(0,0)));


/* Example 2: The curve x^3 + y^3 + z^3 + 6xyz = 0 is isomorphic to the Fermat curve. Gluing it with itself gives the Jacobian of
              C: 2y^2 = (x^3-2)(2x^3-1).
	      Since -3 = (1+2*w)^2 is a square, this is isomorphic to the previous curve over Q(w), but not over Q.
*/
g := map<P3 -> P2 | [x4, x1, -x2+7*x3+x4]>;
h := map<P2 -> P2 | [ (2*X + Z)*(4*X - Z)^2, 27*(2*X-Z)*Y*Z, (4*X - Z)^3 ]>;
h(g(C(2,2)));


/* Example 3: Gluing x^3 + y^3 + z^3 + 6xyz = 0 with the Fermat curve gives the Jacobian of
              C: 2y^2=(x^3 + 6x^2 + 12x + 10)(10x^3 + 36x^2 + 60x + 25).
*/
g := map<P3 -> P2 | [27*x3 + 2*x4, x1, -x2 + 37*x3 + x4]>;
h := map<P2 -> P2 | [5*(8*X - 7*Z)^2*(2*X - Z)*Z^3, 225*Y*(14*X - 11*Z)*Z^4, (8*X - 7*Z)^3*Z^3]>;
h(g(C(0,2)));


/* Example 4: a=2*w, b=2*w^2 again gives 2y^2 = (x^3-2)(2x^3-1) */
g := map<P3 -> P2 | [ 9*x3 - 4*(1+2*w)*x4, x1, -91*(1 + 2*w)*x2 + 7*(9 - 8*(1 + 2*w))*x3 + (-105 - 28*(1 + 2*w))*x4 ]>;
h := map<P2 -> P2 | [ ((392 - 84*w)*X - (21 + 5*w)*Z)*((238 + 196*w)*X + 19*Z)^2, 31941*(1 + 2*w)*(2 + 5*w)^3*(14*X - Z)*Y*Z, ((238 + 196*w)*X + 19*Z)^3 ]>;
h(g(C(2*w,2*w^2)));
