/*  If both f1 and f2 have special ramification then we can assume P(x) = x^2 + ax + b and f1(x) = x^3/P(x) and f2(x)=1/Q(x).
*/

RR<x,y,z,a,b> := PolynomialRing(Rationals(),5);
P := func<u | u^2 + a*u + b >;
Q := func<u | -u^3*a^2 + 4*u^3*b + 2*u^2*a*b + 3*u*b^2 >;
D := func<u | Derivative(Q(u),u) >;
R := Resultant(Q(x) - Q(y), D(y), y);
R := Quotrem(R, D(x)^2);
q,r := Quotrem(R, P(x));
I := ideal< RR | [
  Coefficient(r,x,0),
  Coefficient(r,x,1),
  1 - z * Coefficient(Q(x),x,3) * Resultant(x,P(x),x) * Discriminant(P(x),x) * Discriminant(Q(x),x)
]>;
for p in PrimaryDecomposition(EliminationIdeal(I,3)) do
  Basis(p);
end for;

// The j-invariants
F<a,b> := FunctionField(Rationals(),2);
R<x,y> := PolynomialRing(F,2);
R1<X> := PolynomialRing(F,1);
R2 := PolynomialRing(F);
h1 := hom<R->R1 | [X, 0] >;
h2 := hom<R1->R2 | [R2.1] >;

// Case a=0. This is the only case.
P := func<u | u^2 + b >;
Q := func<u | 4*u^3 + 3*b*u >;
A := h1(Resultant(x*P(y) - y^3, Q(y), y));
A := A/Coefficient(A,X,3);
j1 := jInvariant(EllipticCurve(h2(A)));
B := h1(Resultant(x*Q(y) - 1, P(y), y));
B := B*X; // <-- we add the image of infinity
B := B/Coefficient(B,X,3);
j2 := jInvariant(EllipticCurve(h2(B)));
[j1,j2];

/* Case b = 3*a^2/8. This case shows the limitations of the method. The corresponding curves are NOT complementary.
   Rather, the curve C has an extra involution that permutes the Weierstrass points injust the right way, so that the
   roots of P(x) and the roots of Q(x) are swapped, just as they would be by complementary coverings. In this case,
   composing the covering with the involution does not give the complementary covering. See "gluing_curves/components_of_Jac(C).m"
*/
P := func<u | 8*u^2 + 8*a*u + 3*a^2 >;
Q := func<u | 32*u^3 + 48*a*u^2 + 27*a^2*u >;
A := h1(Resultant(x*P(y) - y^3, Q(y), y));
A := A/Coefficient(A,X,3);
j1 := jInvariant(EllipticCurve(h2(A)));
B := h1(Resultant(x*Q(y) - 1, P(y), y));
B := B*X; // <-- we add the image of infinity
B := B/Coefficient(B,X,3);
j2 := jInvariant(EllipticCurve(h2(B)));
[j1,j2];
