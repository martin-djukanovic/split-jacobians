/*  
  Characteristic of the base field is not 2.
  If a genus-2 curve admits a 3-to-1 map to an elliptic curve E1: y^2 = x^3 + ...., then:
  - C admits another 3-to-1 map C --> E2 to an elliptic curve, and Jac(C) ~ E1 x E2 as ppav.
  - C admits an affine model y^2 = P(x)Q(x) where P(x) and Q(x) are cubic polynomials.
  - the induced degree-3 maps f1: C/invol --> E1/[-1] and f2: C/invol --> E2/[-1] both ramify above the images of E1[2] and E2[2] respectively
    and above one other rational point in the generic case; in special cases all ramification is above the branch locus of E --> E/[-1].
  - a fibre of f1 above a point of E1[2] contains the roots of P(x) (half of the branch locus of C --> C/invol)
  - a fibre of f2 above a point of E2[2] contains the roots of Q(x) (the remaining half)
  - Suppose P(x) = x^3 + a*x^2 + b*x + c and apply linear transformations to ensure that the fibre with roots of P(x) is above infinity
    and that the ramification point not above E1[2] is zero.
  - That means f1(x) = x^2/P(x), f2(x) = (x+d)^2*(x+e)/Q(x)
  - We find Q(x) in terms of P(x) by computing the fibres of f1(x) that contain the ramification
  - Applying the same method to f2(x), we should P(x) back. This determines d and e.
*/
RR<x,y,z,a,b,c,d,e> := PolynomialRing(Rationals(),8);
P := func<u | u^3 + a*u^2 + b*u + c >;
// D is the numerator of f1’(x)/x
D := func<u | u*Derivative(P(u),u) - 2*P(u)>;
// We clear some unnecessary non-zero factors from Q
Q := func<u | Quotrem(Resultant(u^2*P(z) - z^2*P(u), D(z), z), Resultant(u,P(u),u)*D(u)^2) >;
// D2 is the numerator of f2’(x)/(x+d)
D2 := func<u | (u+e)*(u+d)*Derivative(Q(u),u) - Q(u)*(2*(u+e) + (u+d)) >;
R := Resultant((x+d)^2*(x+e)*Q(y) - (y+d)^2*(y+e)*Q(x), D2(y), y);
// We clear some unnecessary non-zero factors from R
R := Quotrem(R, Resultant((x+d)*(x+e),Q(x),x)*D2(x)^2);
q,r := Quotrem(R,P(x)); // r must be 0
I := ideal< RR | [
  Coefficient(r,x,0),
  Coefficient(r,x,1),
  Coefficient(r,x,2),
  // some terms must be non-zero; e.g. discriminant of P(x)Q(x), etc
  1 - z * Resultant((x+d)*(x+e),Q(x),x) * Resultant(x,P(x),x) * Discriminant(P(x),x) * Discriminant(Q(x),x) * Resultant(x+d,x+e,x)
]>;

// print Q(x)
RR!Q(x);
// print the equations that determine d,e in terms of a,b,c
Basis(PrimaryDecomposition(EliminationIdeal(I,3))[1]);


/* Having found f1(x) and f2(x), up to multiplication by constants, we can determine the j-invariants of E1 and E2.
   E1 --> E1/[-1] branches above the image of the zero locus of P(x) and Q(x) under f1 and E2 --> E2/[-1] branches
   above the image under f2.
  */
F<a,b,c,d,e> := FunctionField(Rationals(),5);
R<x,y> := PolynomialRing(F,2);
R1<X> := PolynomialRing(F,1);
R2 := PolynomialRing(F);
h1 := hom<R->R1 | [X, 0] >;
h2 := hom<R1->R2 | [R2.1] >;
P := func<u | u^3 + u^2*a + u*b + c >;
Q := func<u | 4*u^3*c + u^2*b^2 + 2*u*b*c + c^2 >;
N := func<u | (b*u + 3*c)^2 * ((b^3 - 4*a*b*c + 9*c^2)*u + b^2*c - 3*a*c^2) >;
A := h1(Resultant(x*P(y) - y^2, Q(y), y));
A := A/Coefficient(A,X,3);
j1 := jInvariant(EllipticCurve(h2(A)));
B := h1(Resultant(x*Q(y) - N(y), P(y), y));
B := B/Coefficient(B,X,3);
j2 := jInvariant(EllipticCurve(h2(B)));
[j1,j2];
