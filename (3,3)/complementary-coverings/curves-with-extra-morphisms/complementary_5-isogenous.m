/*  Below is a 1-dimensional family of genus-2 curves C with the following properties:
    1) C admits complementary degree-3 maps f1:C-->E1 and f2:C-->E2, where E1 and E2 are elliptic curves
    2) C has an additional involution, that swaps the 3 Weierstrass points that are in the same fibre of f1 (or equivalently f2)
       with the remaining 3 Weierstrass points
   
    The elliptic curves E1 and E2 are then 5-isogenous and the 5-isogeny induces the coverings in the sense that
    Jac(C) = (E1 x E2)/G, where G is the graph of the isomorphism E1[3] --> E2[3] that is the restriction of the
    said isogeny to the 3-torsion.
    
    Therefore this is a 1-dimensional family of curves like those in Example 3.7.

    This family can be found as follows. Since (generically), a genus-2 curve C with a (3,3)-split Jacobian admits a model y^2 = P(x)Q(x),
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


// we eliminate all variables but a,b,c from the ideal generated by the equations
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

/*   The resulting equation describes two genus-0 curves (which we can view in the weighted projective space P(1,2,3) 
     because curves defined by different representatives of [a:b:c] are isomorphic), namely:
     X1: -a^2*b^5 + 8*b^6 + 4*a^3*b^3*c - 54*a*b^4*c + 108*a^2*b^2*c^2 + 27*b^3*c^2 - 108*a^3*c^3 = 0
     X5: a^2*b^5 - 18*a*b^4*c - 28*a^2*b^2*c^2 + 85*b^3*c^2 + 4*a^3*c^3 + 468*a*b*c^3 - 2160*c^4 = 0
    
    The curve X1 is the one from section 3.1.1. It describes genus-2 curves with an additional involution h:C->C and a degree-3 map
    f:C-->E to an elliptic curve E, such that the composition f∘h is complementary to f (i.e. Jac(C) ~ E x E).
    
    The curve X5 parametrizes the new family of curves C that we wish to describe in detail, by first parametrizing X5.
    If char(K)=5, then X5 has an additional component, defined by a=0. The other component can be parametrized in the same way as in general
    characteristic.
*/


/******************************
 CASE 1: any characteristic
/******************************/
PP<a,b,c>:=WeightedProjectiveSpace(QQ,[1,2,3]);
X5:=Scheme(PP, a^2*b^5 - 18*a*b^4*c - 28*a^2*b^2*c^2 + 85*b^3*c^2 + 4*a^3*c^3 + 468*a*b*c^3 - 2160*c^4);
A1<t>:=AffineSpace(QQ,1);

// a parametrization of X5
p:=map<A1->X5| [-(t - 4)*(t^2 + 1), 2*(t + 2)*(t^2 + 1), 2*(t^2 + 1)^2] >;

// taking the representative (a,b,c) = (4 - t, 2*(t + 2)/(t^2 + 1), 2/(t^2 + 1)) gives the following family
K<t>:=FunctionField(QQ);
A2<x,y>:=AffineSpace(K,2);
C:=Curve(A2, -y^2 + ((t^2 + 1)*x^3 - (t - 4)*(t^2 + 1)*x^2 + 2*(t + 2)*x + 2)*(2*(t^2 + 1)*x^3 + (t+2)^2*x^2 + 2*(t + 2)*x + 1));
E1:=Curve(A2, -y^2 + (t - 1)^6*(2*t - 11)*(t^2 + 1)*x^3 + 2*(t - 1)^3*(3*t - 14)*(t^2 + 1)*x^2 + (6*t^3 - 23*t^2 + 10*t - 20)*x + 2);
E2:=Curve(A2, -y^2 + (t^2 + 1)*x^3 - 2*(t - 1)*(t + 32)*(2*t - 11)*(t^2 + 1)*x^2 + (t - 1)^2*(2*t - 11)^2*(108*t^3 + 1233*t^2 + 386*t + 1204)*x - 2*(t - 1)^3*(2*t - 11)^3*(9*t + 13)^3);

// an additional involution on C
inv:=map<C->C | [-(t*x + 1)/((2*t - 1)*x + t), (t - 1)^3*y/((2*t - 1)*x + t)^3]>;

// a simpler model of C
C0:=map<A2->A2|[ (2*t*x - x + 1)/(x + 1),  8*y/(x + 1)^3]>(C);

// the degree-3 maps to elliptic curves E1 and E2
f1:=map<C->E1|[
  x^2/((t^2 + 1)*x^3 - (t - 4)*(t^2 + 1)*x^2 + 2*(t + 2)*x + 2),
  ((t^2 + 1)*x^3 - 2*(t + 2)*x - 4)*y/((t^2 + 1)*x^3 - (t - 4)*(t^2 + 1)*x^2 + 2*(t + 2)*x + 2)^2
]>;
f2:=map<C->E2|[
  (2*t - 11)*((t + 2)*x + 3)^2*((4*t^2 + 2*t - 7)*x + 3*t - 4)/(2*(t^2 + 1)*x^3 + (t+2)^2*x^2 + 2*(t + 2)*x + 1), 
  (2*t - 11)^3*((2*t^4 - 3*t^3 - 4*t^2 + 8*t - 4)*x^3 + (2*t^3 - 7*t^2 + 6*t - 4)*x^2 - (t + 2)*x - 1)*y/(2*(t^2 + 1)*x^3 + (t+2)^2*x^2 + 2*(t + 2)*x + 1)^2
]>;

// a separable 5-isogeny E2 --> E1, with kernel polynomial being the square of (t^2 + 1)*x^2 - 50*(t - 1)*(t^2 + 1)*(2*t - 11)*x + (t - 1)^2*(621*t^2 + 44*t + 504)*(2*t - 11)^2
isog1:=map<E2->E1|[
  (-4*(t - 1)^5*(2*t - 11)^5*(385641*t^6 - 3644298*t^5 + 10235935*t^4 + 1215710*t^3 + 14471640*t^2 + 6984872*t + 5610344) + (t - 1)^4*(2*t - 11)^4*(248400*t^6 - 2396416*t^5 + 7593065*t^4 - 1713840*t^3 + 13784120*t^2 + 1036720*t + 6604288)*x - 4*(t - 1)^3*(2*t - 11)^3*(t^2 + 1)*(3742*t^4 - 36684*t^3 + 127363*t^2 - 15346*t + 131512)*x^2 + 2*(t - 1)^2*(2*t - 11)^2*(t^2 + 1)*(200*t^4 - 1984*t^3 + 8111*t^2 - 1648*t + 8438)*x^3 - 4*(t - 1)*(2*t - 11)*(t^2 + 1)^2*(t^2 - 10*t + 56)*x^4 + (t^2 + 1)^2*x^5)/((t - 1)^4*(2*t - 11)^3*((t - 1)^2*(2*t - 11)^2*(621*t^2 + 44*t + 504) - 50*(t - 1)*(2*t - 11)*(t^2 + 1)*x + (t^2 + 1)*x^2)^2), 
  (-(t - 1)^6*(2*t - 11)^6*(19525536*t^7 - 486414261*t^6 + 966558244*t^5 - 2428404320*t^4 + 2893703760*t^3 - 3061281408*t^2 + 1980853248*t - 1084423552) + 10*(t - 1)^5*(2*t - 11)^5*(t^2 + 1)*(279936*t^5 - 9148615*t^4 + 11307640*t^3 - 24072520*t^2 + 17917680*t - 11027648)*x - 3*(t - 1)^4*(2*t - 11)^4*(t^2 + 1)*(50112*t^5 - 2507805*t^4 + 1619080*t^3 - 4726740*t^2 + 1955360*t - 1901216)*x^2 + 4*(t - 1)^3*(2*t - 11)^3*(t^2 + 1)^2*(896*t^3 - 87409*t^2 + 20812*t - 60822)*x^3 - (t - 1)^2*(2*t - 11)^2*(t^2 + 1)^2*(32*t^3 - 9683*t^2 + 484*t - 8044)*x^4 - 150*(t - 1)*(2*t - 11)*(t^2 + 1)^3*x^5 + (t^2 + 1)^3*x^6)*y/((t - 1)^3*(2*t - 11)^4*((t - 1)^2*(2*t - 11)^2*(621*t^2 + 44*t + 504) - 50*(t - 1)*(2*t - 11)*(t^2 + 1)*x + (t^2 + 1)*x^2)^3)
]>;

// the dual 5-isogeny E1 --> E2 with kernel polynomial being the square of 5*(t^2 + 1)*(t - 1)^6*x^2 + 10*(t^2 + 1)*(t - 1)^3*x + 5*t^2 + 4 if char(K)!=5
isog2:=map<E1->E2|[
	((t - 1)*(2*t - 11)*((2*t - 11)^2*(t^2 + 1)^2*(t - 1)^15*x^5 + 20*(t^2 + 1)^2*(t^2 - 10*t + 56)*(t - 1)^12*x^4 + 10*(t^2 + 1)*(4*t^4 - 36*t^3 + 335*t^2 - 60*t + 338)*(t - 1)^9*x^3 + 20*(t^2 + 1)*(2*t^4 - 16*t^3 + 223*t^2 - 50*t + 208)*(t - 1)^6*x^2 + 5*(4*t^6 - 28*t^5 + 565*t^4 - 184*t^3 + 976*t^2 - 176*t + 400)*(t - 1)^3*x + 4*(t^6 - 6*t^5 + 171*t^4 - 62*t^3 + 244*t^2 - 80*t + 56)))/(5*(t^2 + 1)*(t - 1)^6*x^2 + 10*(t^2 + 1)*(t - 1)^3*x + 5*t^2 + 4)^2,
    ((t - 1)^3*(2*t - 11)^3*((2*t - 11)*(t^2 + 1)^3*(t - 1)^18*x^6 + 6*(2*t - 11)*(t^2 + 1)^3*(t - 1)^15*x^5 + (t^2 + 1)^2*(30*t^3 - 165*t^2 + 8*t - 144)*(t - 1)^12*x^4 + 4*(t^2 + 1)^2*(10*t^3 - 55*t^2 - 12*t - 46)*(t - 1)^9*x^3 + 3*(t^2 + 1)*(10*t^5 - 55*t^4 - 24*t^3 - 116*t^2 - 48*t - 64)*(t - 1)^6*x^2 + 2*(t^2 + 1)*(6*t^5 - 33*t^4 - 32*t^3 - 96*t^2 - 80*t - 80)*(t - 1)^3*x + 2*t^7 - 11*t^6 - 16*t^5 - 60*t^4 - 80*t^3 - 112*t^2 - 64*t - 64)*y)/(5*(t^2 + 1)*(t - 1)^6*x^2 + 10*(t^2 + 1)*(t - 1)^3*x + 5*t^2 + 4)^3
]>;  

// the dual isogeny if char(K)=5 is inseparable:
// isog2:=map<E1->E2|[3*(t + 2)^5*(t + 3)^2*(t + 4)^16*x^5 + 3*(t^2 - 1)*(t + 2)^2*(t^4 + t^3 + t^2 + 3*t + 3), (t + 2)^3*(t + 3)*(t + 4)^9*y^5]>;


/* A model of C on which an involution is given by (x,y)->(-x,y) is defined by x -> ((2*t - 1)*x + 1)/(x + 1).
   Composing with (x,y)->(x^2,y) or (x,y)->(1/x^2,y/x^3) gives the compolementary degree-2 covering maps.
   As it turns out, C covers 2-to-1 the same two curves that it covers 3-to-1.  */
g1:=map<C->E1|[
   -(2*(2*t + 1)*(t^2 + 1)*x^2 + (4*t^2 + 4*t + 7)*x + t + 2)/((t - 1)^2*(t^2 + 1)*((2*t - 1)*x + 1)^2),
   (2*t - 11)*y/((t - 1)*(t^2 + 1)*((2*t - 1)*x + 1)^3)
]>;
g2:=map<C->E2|[
   ((t - 1)*(2*t - 11)*(2*(t + 7)*(t^2 + 1)*x^2 + (56*t^2 - 31*t + 39)*x + 27*t^2 - 9*t + 14))/((t^2 + 1)*(x + 1)^2),
   ((t - 1)^2*(2*t - 11)^3*y)/((t^2 + 1)*(x + 1)^3)
]>;


// the j-invariants of the two elliptic curves
R:=PolynomialRing(K);
h:=hom<CoordinateRing(A2)->R|[R.1, 0]>;
j1:=jInvariant(EllipticCurve(h(Basis(Ideal(E1))[1])/((t - 1)^6*(2*t - 11)*(t^2 + 1))));
j2:=jInvariant(EllipticCurve(h(Basis(Ideal(E2))[1])));
j1 eq 64*(t^2 + 114*t + 124)^3/(2*t - 11)^5;
j2 eq 64*(t^2 - 6*t + 4)^3/(2*t - 11);


/* We can remove the factor (t-1) from C0 and use that simpler model instead */
R<x>:=PolynomialRing(K);
C:=HyperellipticCurve(x^6 + (-4*t^2 + 12*t + 5)*x^4 + (8*t^2 + 72*t - 13)*x^2 - (2*t - 11)^2);
E1:=EllipticCurve(x^3 + 2*(3*t - 14)*(t^2 + 1)*x^2 + (2*t - 11)*(t^2 + 1)*(6*t^3 - 23*t^2 + 10*t - 20)*x + 2*(2*t - 11)^2*(t^2 + 1)^2*(t - 1)^3);
E2:=EllipticCurve(x^3 - 2*(t + 32)*(2*t - 11)*(t^2 + 1)*x^2 + (2*t - 11)^2*(t^2 + 1)*(108*t^3 + 1233*t^2 + 386*t + 1204)*x - 2*(2*t - 11)^3*(t^2 + 1)^2*(9*t + 13)^3);
IsIsomorphic(IsogenyFromKernel(E2, (x^2 - 50*(t^2 + 1)*(2*t - 11)*x + (t^2 + 1)*(621*t^2 + 44*t + 504)*(2*t - 11)^2)^2, E1);
L<x,y>:=FunctionField(C);
f1:=map<C->E1|[
-(2*t - 11)*(t^2 + 1)*(x + 1)^2*(2*t + x - 1)/(2*t*x^2 + 4*t*x + 2*t + x^3 - x^2 + 3*x - 11), 
 (2*t - 11)*(t^2 + 1)*y*(8*t*x - 24*t - x^3 + 5*x^2 - 19*x + 7)/(2*t*x^2 + 4*t*x + 2*t + x^3 - x^2 + 3*x - 11)^2,
 1
]>;
f2:=map<C->E2|[
  -(t^2 + 1)*(2*t - 11)*(x - 5)^2*(4*t*x - 2*t + 3*x + 11)/(2*t*x^2 - 4*t*x + 2*t - x^3 - x^2 - 3*x - 11), 
   (t^2 + 1)*(2*t - 11)^3*y*(2*t*x^3 + 2*t*x^2 - 2*t*x - 2*t + x^3 + 9*x^2 + 11*x + 11)/(2*t*x^2 - 4*t*x + 2*t - x^3 - x^2 - 3*x - 11)^2,
 1
]>;


/*******************************
 CASE 2: only characteristic 5
 This family will capture some additional cases, such as C: y^2 = x^6 - 1, but it is otherwise covered by the previous family if char(K)=5
 Other isomorphism classes are already captured by CASE 1 in characteristic 5.
/*******************************/
K<t>:=FunctionField(GF(5));
A2<x,y>:=AffineSpace(K,2);
C:=Curve(A2, -y^2 + (x^3 + t*x + 1)*(x^3 - t^2*x^2 + 3*t*x - 1));
E1:=Curve(A2, -y^2 + x^3 + 3*t*x^2 + t^2*(t^3+3)*x + (t^3 + 3)^2);
E2:=Curve(A2, -y^2 + x^3 + 2*t^2*(t^3 + 3)*x^2 + t*(t^3+3)^2*(t^3+2)^2*x + 3*(t^3+3)^3*(t^3+1)^3);

// an additional involution on C
inv:=map<C->C|[ -x/(t*x + 1), y/(t*x + 1)^3 ]>;

// a simpler model for C
map<A2->A2|[-t*(t*x+2)/(t*x), t^3*y/(t*x)^3]>(C);

// the degree-3 maps to elliptic curves E1 and E2
f1:=map<C->E1|[
    -(t^3 + 3) * x^2/(x^3 + t*x + 1), 
     (t^3 + 3) * y*((x^3 - t*x + 3)/(x^3 + t*x + 1)^2)
]>;
f2:=map<C->A2|[
    (t^3 + 3) * (t*x - 2)^2*((t^3 - 1)*x + t^2)/(x^3 - t^2*x^2 + 3*t*x - 1),
    (t^3 + 3)^2 * y*((t^6 + t^3 - 1)*x^3 + t^2*(t^3 + 3)*x^2 + 2*t*(2*t^3 + 1)*x + 2*(2*t^3 + 1))/(x^3 - t^2*x^2 + 3*t*x - 1)^2
]>;


// a separable 5-isogeny E1-->E2
isog1:=map<E1->E2|[
  -(t^3 + 3)*(((t^3 + 3)*x^5 + 3*t*x^4 - t^2*(t^3 + 3)^2*x^3 - t^3*(t^3 + 3)^2*x^2 - t*(t^3 + 3)^4*x + t^2*(t^3 + 3)^4)/(t*x^2 + 3*(t^3 + 3)^2)^2), 
   (t^3 + 3)^3 * y * ((2*x^6 + 2*t^2*(t^3 + 3)*x^4 - (t^3 + 3)^2*x^3 + 3*t*(t^3 + 3)^3*x^2 - (t^3 + 3)^5)/(t*x^2 + 3*(t^3 + 3)^2)^3)
]>;

// and its inseparable dual 5-isogeny E2-->E1
isog2:=map<E2->E1|[ 1/(t^3+3)^10 * x^5 - t*(t^15 + t^9 + 3)/(t^3+3)^5, 1/(t^3+3)^15 * y^5 ]>;


// the degree-2 maps to the same two elliptic curves
C2:=map<A2->A2|[-2*x/(t*x + 2), y/(t*x + 2)^3]>(C);
g1:=map<C2->E1|[-(t^6 + t^3 - 1)*x^2 - t*(t^3 + 3), 2*(t^2 + 3*t - 1)^2*(2*t - 1)^2*y]>;
g2:=map<C2->E2|[(t^3 + 3)^2/x^2 + t^8 + 2*t^5 + 2*t^2, (t^3 + 3)^3*y/x^3]>;


// the j-invariants of the two elliptic curves
R:=PolynomialRing(K);
h:=hom<Parent(x)->R|[R.1,0]>;
j1:=jInvariant(EllipticCurve(h(Basis(Ideal(E1))[1])));
j2:=jInvariant(EllipticCurve(h(Basis(Ideal(E2))[1])));
j2 eq 3*t^3/(t^3 + 3) and j1 eq j2^5;
