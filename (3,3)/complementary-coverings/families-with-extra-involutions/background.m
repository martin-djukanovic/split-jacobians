/* We are looking for curves C: y^2=P(x)Q(x), with P(x)=x^3 + a*x^2 + b*x + c and Q(x)=4*c*x^3 + b^2*x^2 + 2*b*c*x + c^2, that admit
   involutions other than the hyperelliptic one. To that end, we look for fractional linear transformations of the form M(x)=(p*x+q)/(r*x-p)
   (these are exactly the transformations that satisfy M(M(x))=x and are not the identity map, if p^2+q*r is non-zero) that permute the roots
   of the sextic P(x)Q(x). This can be expressed in terms of resultants: the resultant of x - M(y) and P(y)Q(y) should be divisible by P(x)Q(x). */

K<p,q,r,a,b,c>:=FunctionField(QQ,6);
R<x,y>:=PolynomialRing(K,2);
P:=func<x | x^3 + a*x^2 + b*x + c >;
Q:=func<x | 4*c*x^3 + b^2*x^2 + 2*b*c*x + c^2 >;
res:=Resultant((r*y-p)*x - (p*y+q), P(y)*Q(y), y);
_,rem:=Quotrem(res, P(x)*Q(x));
rem:=rem*4*c; // c is not zero if C is of genus 2

// r must be zero and this leads to the following six equations
eqns:=[Coefficient(rem,x,k) : k in [0..5]];

/* We eliminate the variables p,q,r from the equations and also impose the condition of C having a non-zero discriminant
   and M(x) being non-constant. */
R<z,p,q,r,a,b,c>:=PolynomialRing(QQ,7);
h:=hom<K->R|[p,q,r,a,b,c]>;
eqns:=[h(g) : g in eqns] cat [1-z*(p^2+q*r)*c*(b^3 - 27*c^2)*(-a^2*b^2 + 4*b^3 + 4*a^3*c - 18*a*b*c + 27*c^2)];
I:=ideal<R | eqns >;
J:=Radical(EliminationIdeal(I,4));

// There are three possible cases:
Factorization(Basis(J)[1]);

/* The resulting genus-0 curves are
   X1: -a^2*b^5 + 8*b^6 + 4*a^3*b^3*c - 54*a*b^4*c + 108*a^2*b^2*c^2 + 27*b^3*c^2 - 108*a^3*c^3 = 0
   X5: a^2*b^5 - 18*a*b^4*c - 28*a^2*b^2*c^2 + 85*b^3*c^2 + 4*a^3*c^3 + 468*a*b*c^3 - 2160*c^4 = 0
   X8: -16*a^4*b^10 + 81*a^2*b^11 - 324*b^12 + 32*a^5*b^8*c + 54*a^3*b^9*c + 2250*a*b^10*c + 320*a^4*b^7*c^2 - 16535*a^2*b^8*c^2 + 16929*b^9*c^2 - 1280*a^5*b^5*c^3 + 24624*a^3*b^6*c^3 - 69300*a*b^7*c^3 - 10864*a^4*b^4*c^4 +443087*a^2*b^5*c^4 - 333187*b^6*c^4 + 11168*a^5*b^2*c^5 - 781106*a^3*b^3*c^5 + 274410*a*b^4*c^5 + 128*a^6*c^6 + 374040*a^4*b*c^6 - 1503225*a^2*b^2*c^6 + 3459375*b^3*c^6 + 2092500*a^3*c^7 - 1215000*a*b*c^7 - 11390625*c^8 = 0
   
   The family of genus-2 curves C with a Jacobian that is (3,3)-isogenous to E1 x E2 that is parametrized by X1 (resp. X5, resp. X8) is
   such that E1 and E2 are isomorphic (resp. 5-isogenous, resp. 8-isogenous). */



/* The family defined by X5 is also precisely the family determined by the second primary component of the final elimination ideal computed
   when analysing the generic case. */
RR<x,y,z,d,e,a,b,c> := PolynomialRing(QQ,8);
P := func<u | u^3 + a*u^2 + b*u + c >;
D := func<u | u*Derivative(P(u),u) - 2*P(u)>;
Q := func<u | Quotrem(Resultant(u^2*P(z) - z^2*P(u), D(z), z), Resultant(u,P(u),u)*D(u)^2) >;
D2 := func<u | (u+e)*(u+d)*Derivative(Q(u),u) - Q(u)*(2*(u+e) + (u+d)) >;
R := Resultant((x+d)^2*(x+e)*Q(y) - (y+d)^2*(y+e)*Q(x), D2(y), y);
R := Quotrem(R, Resultant((x+d)*(x+e),Q(x),x)*D2(x)^2);
q,r := Quotrem(R,P(x));
I := ideal< RR | [
  Coefficient(r,x,0),
  Coefficient(r,x,1),
  Coefficient(r,x,2),
  1 - z * Resultant((x+d)*(x+e),Q(x),x) * Resultant(x,P(x),x) * Discriminant(P(x),x) * Discriminant(Q(x),x) * Resultant(x+d,x+e,x)
]>;
J := PrimaryDecomposition(EliminationIdeal(I,3))[2];
Basis(EliminationIdeal(J,5))[1];
