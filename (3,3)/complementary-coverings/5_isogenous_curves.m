/*  Below is a 1-dimensional family of genus-2 curves C with the following properties:
    1) C admits complementary degree-3 maps f1:C-->E1 and f1:C-->E2, where E1 and E2 are elliptic curves
    2) C has an additional involution, that swaps the 3 Weierstrass points that are in the same fibre of f1 (or equivalently f2)
       with the remaining 3 Weierstrass points
   
    The elliptic curves E1 and E2 are then 5-isogenous and the 5-isogeny induces the coverings in the sense that
    Jac(C) = (E1 x E2)/G, where G is the graph of the isomorphism E1[3] --> E2[3] that is the restriction of the
    said isogeny to the 3-torsion.
    
    Therefore this is a 1-dimensional family of curves like those in Example 3.7.

    This family is found as follows. Since (generically), a genus-2 curve C with a (3,3)-split Jacobian admits a model y^2 = P(x)Q(x),
    where P(x)=x^3 + a*x^2 + b*x + c and Q(x)=4*c*x^3 + b^2*x^2 + 2*b*c*x + c^2, we look for curves with automorphisms that swap the roots
    of P(x) with the roots of Q(x). To that end, we look for fractional linear transformations M(x)=(px+q)/(rx+s) that accomplish this and we 
    express this condition via resultants.
*/

K<p,q,r,s,a,b,c>:=FunctionField(QQ,7);
R<x,y>:=PolynomialRing(K,9);
P:=func<x | x^3 + a*x^2 + b*x + c >;
Q:=func<x | 4*c*x^3 + b^2*x^2 + 2*b*c*x + c^2 >;
R1 := Resultant((r*y+s)*x - (p*y+q), P(y), y);
R2 := Resultant((r*y+s)*x - (p*y+q), Q(y), y);
_,r1 := Quotrem(R1, Q(x));
_,r2 := Quotrem(R2, P(x));

// r1 and r2 must be zero, which gives the following equations:
eqns:=[
  Coefficient(r1,x,0),
  Coefficient(r1,x,1),
  Coefficient(r1,x,2),
  Coefficient(r2,x,0),
  Coefficient(r2,x,1),
  Coefficient(r2,x,2)
];


// we eliminate all variables but a,b,c
R<z,p,q,r,s,a,b,c>:=PolynomialRing(QQ,9);
I := ideal< R | [
  -4*c*p^3 + 4*b*p^2*q - 4*a*p*q^2 + 4*q^3 - c^2*r^3 + b*c*r^2*s - a*c*r*s^2 + c*s^3, 
  6*c*p^2*r - 4*b*p*q*r + 2*a*q^2*r - b*c*r^3 - 2*b*p^2*s + 4*a*p*q*s - 6*q^2*s + b^2*r^2*s - a*b*r*s^2 + b*s^3, 
  -12*c^2*p*r^2 + 4*b*c*q*r^2 - b^2*c*r^3 + 8*b*c*p*r*s - 8*a*c*q*r*s + b^3*r^2*s - 4*a*c*p*s^2 + 12*c*q*s^2 - 
   a*b^2*r*s^2 + b^2*s^3, (-c^2)*p^3 + 2*b*c*p^2*q - b^2*p*q^2 + 4*c*q^3 - c^3*r^3 + 2*b*c^2*r^2*s - b^2*c*r*s^2 + 
   4*c^2*s^3, 3*c^2*p^2*r - 4*b*c*p*q*r + b^2*q^2*r - b*c^2*r^3 - 2*b*c*p^2*s + 2*b^2*p*q*s - 12*c*q^2*s + 
   2*b^2*c*r^2*s - b^3*r*s^2 + 4*b*c*s^3, -3*c^2*p*r^2 + 2*b*c*q*r^2 - a*c^2*r^3 + 4*b*c*p*r*s - 2*b^2*q*r*s + 
   2*a*b*c*r^2*s - b^2*p*s^2 + 12*c*q*s^2 - a*b^2*r*s^2 + 4*a*c*s^3,
  
  // the discriminant of P(x)Q(x) and the determinant of M are non-zero
  1-z*(p*q-r*s)*c*(b^3 - 27*c^2)*(-a^2*b^2 + 4*b^3 + 4*a^3*c - 18*a*b*c + 27*c^2)
]>;
PrimaryDecomposition(EliminationIdeal(I,5));

/*   The two equations above describe genus-0 curves in the weighted projective space P(1,2,3), namely:
     X1: -a^2*b^5 + 8*b^6 + 4*a^3*b^3*c - 54*a*b^4*c + 108*a^2*b^2*c^2 + 27*b^3*c^2 - 108*a^3*c^3 = 0
     X3: a^2*b^5 - 18*a*b^4*c - 28*a^2*b^2*c^2 + 85*b^3*c^2 + 4*a^3*c^3 + 468*a*b*c^3 - 2160*c^4 = 0
    
    The curve X1 is the one from section 3.1.1. It describes genus-2 curves with an additional involution h:C->C and a degree-3 map
    f:C-->E to an elliptic curve E, such that the composition f∘h is complementary to f (i.e. Jac(C) ~ E x E).
    
    The curve X3 parametrizes the new family of curves C that we wish to describe in detail.
*/

// X3 as a curve in the weighted projective space P(1,2,3); curves defined by different representatives of [a:b:c] are isomorphic.
PP<a,b,c>:=WeightedProjectiveSpace(QQ,[1,2,3]);
X3:=Scheme(PP, a^2*b^5 - 18*a*b^4*c - 28*a^2*b^2*c^2 + 85*b^3*c^2 + 4*a^3*c^3 + 468*a*b*c^3 - 2160*c^4);
A1<t>:=AffineSpace(QQ,1);

// a parametrization of X3
map<A1->X3| [-(t - 4)*(t^2 + 1), 2*(t + 2)*(t^2 + 1), 2*(t^2 + 1)^2]>;

// taking the representative (a,b,c) = (4 - t, 2*(t + 2)/(t^2 + 1), 2/(t^2 + 1)) gives the following family
K<t>:=FunctionField(QQ);
A2<x,y>:=AffineSpace(K,2);
C:=Curve(A2, -y^2 + ((t^2 + 1)*x^3 - (t - 4)*(t^2 + 1)*x^2 + 2*(t + 2)*x + 2)*(2*(t^2 + 1)*x^3 + (t+2)^2*x^2 + 2*(t + 2)*x + 1));
E1:=Curve(A2, - y^2 + (t - 1)^6*(2*t - 11)*(t^2 + 1)*x^3 + 2*(t - 1)^3*(3*t - 14)*(t^2 + 1)*x^2 + (6*t^3 - 23*t^2 + 10*t - 20)*x + 2);
E2:=Curve(A2, - y^2 + (t^2 + 1)*x^3 - 2*(t - 1)*(t + 32)*(2*t - 11)*(t^2 + 1)*x^2 + (t - 1)^2*(2*t - 11)^2*(108*t^3 + 1233*t^2 + 386*t + 1204)*x - 2*(t - 1)^3*(2*t - 11)^3*(9*t + 13)^3);

// the additional involution on C
inv:=map<C->C | [-(t*x + 1)/((2*t - 1)*x + t), (t - 1)^3*y/((2*t - 1)*x + t)^3]>;

// the degree-3 maps to elliptic curves E1 and E2
f1:=map<C->E1|[
  x^2/((t^2 + 1)*x^3 - (t - 4)*(t^2 + 1)*x^2 + 2*(t + 2)*x + 2),
  ((t^2 + 1)*x^3 - 2*(t + 2)*x - 4)*y/((t^2 + 1)*x^3 - (t - 4)*(t^2 + 1)*x^2 + 2*(t + 2)*x + 2)^2
]>;
f2:=map<C->E2|[
  (2*t - 11)*((t + 2)*x + 3)^2*((4*t^2 + 2*t - 7)*x + 3*t - 4)/(2*(t^2 + 1)*x^3 + (t+2)^2*x^2 + 2*(t + 2)*x + 1), 
  (2*t - 11)^3*((2*t^4 - 3*t^3 - 4*t^2 + 8*t - 4)*x^3 + (2*t^3 - 7*t^2 + 6*t - 4)*x^2 - (t + 2)*x - 1)*y/(2*(t^2 + 1)*x^3 + (t+2)^2*x^2 + 2*(t + 2)*x + 1)^2
]>;

// the 5-isogeny E2 --> E1
isog5:=map<E2->E1|[
(-4*(-1 + t)^5*(-11 + 2*t)^5*(5610344 + 6984872*t + 14471640*t^2 + 1215710*t^3 + 10235935*t^4 - 3644298*t^5 + 385641*t^6) + 
    (-1 + t)^4*(-11 + 2*t)^4*(6604288 + 1036720*t + 13784120*t^2 - 1713840*t^3 + 7593065*t^4 - 2396416*t^5 + 248400*t^6)*x - 4*(-1 + t)^3*(-11 + 2*t)^3*(1 + t^2)*(131512 - 15346*t + 127363*t^2 - 36684*t^3 + 3742*t^4)*
     x^2 + 2*(-1 + t)^2*(-11 + 2*t)^2*(1 + t^2)*(8438 - 1648*t + 8111*t^2 - 1984*t^3 + 200*t^4)*x^3 - 4*(-1 + t)*(-11 + 2*t)*(1 + t^2)^2*(56 - 10*t + t^2)*x^4 + (1 + t^2)^2*x^5)/
   ((-1 + t)^4*(-11 + 2*t)^3*((-1 + t)^2*(-11 + 2*t)^2*(504 + 44*t + 621*t^2) - 50*(-1 + t)*(-11 + 2*t)*(1 + t^2)*x + (1 + t^2)*x^2)^2), 
  ((-(-1 + t)^6)*(-11 + 2*t)^6*(-1084423552 + 1980853248*t - 3061281408*t^2 + 2893703760*t^3 - 2428404320*t^4 + 966558244*t^5 - 486414261*t^6 + 19525536*t^7) + 
    10*(-1 + t)^5*(-11 + 2*t)^5*(1 + t^2)*(-11027648 + 17917680*t - 24072520*t^2 + 11307640*t^3 - 9148615*t^4 + 279936*t^5)*x - 
    3*(-1 + t)^4*(-11 + 2*t)^4*(1 + t^2)*(-1901216 + 1955360*t - 4726740*t^2 + 1619080*t^3 - 2507805*t^4 + 50112*t^5)*x^2 + 4*(-1 + t)^3*(-11 + 2*t)^3*(1 + t^2)^2*(-60822 + 20812*t - 87409*t^2 + 896*t^3)*x^3 - 
    (-1 + t)^2*(-11 + 2*t)^2*(1 + t^2)^2*(-8044 + 484*t - 9683*t^2 + 32*t^3)*x^4 - 150*(-1 + t)*(-11 + 2*t)*(1 + t^2)^3*x^5 + (1 + t^2)^3*x^6)*
   (y/((-1 + t)^3*(-11 + 2*t)^4*((-1 + t)^2*(-11 + 2*t)^2*(504 + 44*t + 621*t^2) - 50*(-1 + t)*(-11 + 2*t)*(1 + t^2)*x + (1 + t^2)*x^2)^3))
]>;

// j(E1) = -64*(124*t^2 + 114*t + 1)^3/(t*(11*t - 2)^5)
// j(E2) = -64*(4*t^2 - 6*t + 1)^3/(t^5*(11*t - 2))
