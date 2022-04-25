/*  If f1 has generic ramification, but f2 does not, then we assume that f1(x)=x^2/P(x) and f2(x)=(x+d)^3/Q(x).
    The rest is the same as in the generic case
*/
RR<x,y,z,a,b,c,d> := PolynomialRing(Rationals(),7);
P := func<u | u^3 + a*u^2 + b*u + c >;
Q := func<u | 4*u^3*c + u^2*b^2 + 2*u*b*c + c^2 >;
D2 := func<u | (u+d)^2*Derivative(Q(u),u) - 3*(u+d)*Q(u) >;
R := Resultant((x+d)^3*Q(y) - (y+d)^3*Q(x), D2(y), y);
R := Quotrem(R, Resultant((x+d)^2,Q(x),x)*D2(x)^2);
q,r := Quotrem(R, P(x));
I := ideal< RR | [
    Coefficient(r,x,0),
    Coefficient(r,x,1),
    Coefficient(r,x,2),
    1 - z * Coefficient(Q(x),x,3) * Resultant((x+d),Q(x),x) * Resultant(x,P(x),x) * Discriminant(P(x),x) * Discriminant(Q(x),x)
]>;
// print the equations that determine a,d in terms of b,c
Basis(PrimaryDecomposition(EliminationIdeal(I,3))[1]);

// print the j-invariants of E1 and E2
F<b,c> := FunctionField(Rationals(),2);
R<x,y> := PolynomialRing(F,2);
R1<X> := PolynomialRing(F,1);
R2 := PolynomialRing(F);
h1 := hom<R->R1 | [X, 0] >;
h2 := hom<R1->R2 | [R2.1] >;
P := func<u | (b*u + 3*c)*(9*c*u^2 + 2*b^2*u + 3*b*c) >;
Q := func<u | 4*u^3*c + u^2*b^2 + 2*u*b*c + c^2 >;
N := func<u | (b*u + 3*c)^3 >;
A := h1(Resultant(x*P(y) - y^2, Q(y), y));
A := A/Coefficient(A,X,3);
j1 := jInvariant(EllipticCurve(h2(A)));
B := h1(Resultant(x*Q(y) - N(y), P(y), y));
B := B/Coefficient(B,X,3);
j2 := jInvariant(EllipticCurve(h2(B)));
[j1,j2];
