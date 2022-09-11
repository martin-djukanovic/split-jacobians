/* Here we describe families of genus-2 curves C:y^2=P(x)Q(X)=(x^3 + a*x^2 + b*x + c)*(4*c*x^3 + b^2*x^2 + 2*b*c*x + c^2) whose Jacobian is
   (3,3)-isogenous to E1 x E2, where E1 and E2 are elliptic curves that are each other's twist.
   
   We have already established that there are two 1-dimensional families of such curves, namely those parametrized by the curves:
    X1: 4*a^3*b^3*c - 108*a^3*c^3 - a^2*b^5 + 108*a^2*b^2*c^2 - 54*a*b^4*c + 8*b^6 + 27*b^3*c^2 = 0
    Y1: 16*a^6*b^6 - 864*a^6*b^3*c^2 + 11664*a^6*c^4 - 324*a^5*b^5*c + 8748*a^5*b^2*c^3 - 81*a^4*b^7 + 14580*a^4*b^4*c^2 - 157464*a^4*b*c^4 - 864*a^3*b^6*c -
    215784*a^3*b^3*c^3 + 78732*a^3*c^5 + 324*a^2*b^8 + 30618*a^2*b^5*c^2 + 2125764*a^2*b^2*c^4 - 5832*a*b^7*c - 314928*a*b^4*c^3 - 6377292*a*b*c^5 +
    37908*b^6*c^2 + 255879*b^3*c^4 + 8503056*c^6 = 0
    
    By finding suitable parametrizations for these curves, we get a simple description of these families.  */


/***************************
 The family defined by X1.
****************************/
PP<a,b,c>:=WeightedProjectiveSpace(QQ,[1,2,3]);
A1<t>:=AffineSpace(QQ,1);
X1:=Scheme(PP, 4*a^3*b^3*c - 108*a^3*c^3 - a^2*b^5 + 108*a^2*b^2*c^2 - 54*a*b^4*c + 8*b^6 + 27*b^3*c^2);

// a parametrization of X1
p:=map<A1->X1|[ 3*(t + 1)*(t + 3), 48*(t + 1)*t^2, 64*(3*t + 1)*t^3 ]>;

// This choice leads to the following choice of parametrizations of the curves (with the obvious modifications for their quadratic twists).
K<t>:=FunctionField(QQ);
A2<x,y>:=AffineSpace(K,2);
C:=Curve(A2, -y^2 + (4*t*x^3 + 3*(t + 1)*(t + 3)*x^2 + 12*t*(t + 1)*x + 4*t*(3*t + 1))*(4*(3*t + 1)*x^3 + 9*(t + 1)^2*x^2 + 6*(t + 1)*(3*t + 1)*x + (3*t + 1)^2));
E1:=Curve(A2, -y^2 + x^3 + 3*(t + 1)*t*x^2 - 3*(t + 1)*(2*t^2 + 9*t + 3)*t^2*x/(t^2 - 6*t - 3) + (3*t + 1)*t^3);
E2:=Curve(A2, -(t^2 - 6*t - 3)*y^2 + x^3 + 3*(t + 1)*t*x^2 - 3*(t + 1)*(2*t^2 + 9*t + 3)*t^2/(t^2 - 6*t - 3)*x + (3*t + 1)*t^3);
// note that E1 and E2 are clearly twists of each other

// complementary degree-3 maps
f1:=map<C->E1|[
  3*t*(t^2 - 6*t - 3) * x^2/(4*t*x^3 + 3*(t + 1)*(t + 3)*x^2 + 12*t*(t + 1)*x + 4*t*(3*t + 1)), 
  4*t^3 * y*(x^3 - 3*(t + 1)*x - 2*(3*t + 1))/(4*t*x^3 + 3*(t + 1)*(t + 3)*x^2 + 12*t*(t + 1)*x + 4*t*(3*t + 1))^2
]>;
f2:=map<C->E2|[
  3*t/(t^2 - 6*t - 3) * ((t + 1)*x + (3*t + 1))^2*(4*(2*t + 1)*x + (t + 1)*(3*t + 1))/(4*(3*t + 1)*x^3 + 9*(t + 1)^2*x^2 + 6*(t + 1)*(3*t + 1)*x + (3*t + 1)^2), 
  4*t^3/(t^2 - 6*t - 3)^2 * y*((9*t^3 - 105*t^2 - 109*t - 27)*x^3 - 3*(7*t + 3)*(t + 1)*(3*t + 1)*x^2 - 3*t*(t + 1)*(3*t + 1)^2*x - t*(3*t + 1)^3)/(4*(3*t + 1)*x^3 + 9*(t + 1)^2*x^2 + 6*(t + 1)*(3*t + 1)*x + (3*t + 1)^2)^2
]>;

R<X>:=PolynomialRing(K);
h:=hom<CoordinateRing(A2)->R | [X,0]>;
j:=jInvariant(EllipticCurve(h(Basis(Ideal(E1))[1])));
j eq 27*(t - 3)^3*(t + 1)^3/t^3;

// After extending K if necessary, C admits a non-hyperelliptic involution and E1 and E2 are isomorphic, via (x,y) |--> (x,q*y).
K<q>:=ext<K|X^2 - (t^2 - 6*t - 3)>;
A2<x,y>:=AffineSpace(K,2);
R<X>:=PolynomialRing(K);
C:=Curve(A2, -y^2 + (4*t*x^3 + 3*(t + 1)*(t + 3)*x^2 + 12*t*(t + 1)*x + 4*t*(3*t + 1))*(4*(3*t + 1)*x^3 + 9*(t + 1)^2*x^2 + 6*(t + 1)*(3*t + 1)*x + (3*t + 1)^2));

// an involution on C
inv:=map<C->C|[
 -(3*t + 1)*((t + 1)*x + 3*t + 1)/(4*(2*t + 1)*x + (3*t + 1)*(t + 1)),
 -y*q*(3*t + 1)^3*(t^2 - 6*t - 3)/(4*(2*t + 1)*x + (3*t + 1)*(t + 1))^3
]>;

/* The composition f1∘inv is the same map as f2 post-composed with the isomorphism (x,y) |--> (x,q*y).
   Note: if s is a K-rational parameter, we can set t:=-(s^2 + s + 1)/(2*s^2 + s) so that q:=(s^2+ 4*s + 1)/(2*s^2 + s)
   to generate a 1-dimensional family of examples over K. */

/* After applying an isomorphism, the extra involution becomes x->-x, so that degree-2 coverings becomes x->x^2 and x->1/x^2
   iso:=map<C->A2|[(1 - q + 4*t - 3*q*t + 3*t^2 + 4*x + 8*t*x)/(1 + 3*t + x - q*x + t*x), y/(1 + 3*t + x - q*x + t*x)^3]>;
   C2:=iso(C);
   map<C2->C2|[-x,y]>; */

// The involution on C induces degree-2 coverings of (isogenous) elliptic curves, defined over K(q).
F1:=Curve(A2, -(-3*(t - 3)*(3*t + 1)*(t^2 - 6*t - 3) + 3*q*(3*t + 1)*(t^2 - 6*t + 3))*y^2
	+ x^3
	+ 3*(q*(9*t^3 - 33*t^2 - 3*t - 1) - (9*t^4 - 60*t^3 + 42*t^2 + 44*t + 3))*x^2
	- 12*(q*(3*t^3 + 13*t^2 - 33*t - 3) - t*(t + 6)*(3*t^2 - 14*t - 6))*x
	+ 12*(q*(t - 3)*(t^2 - 6*t + 3) - (t^4 - 12*t^3 + 42*t^2 - 36*t - 9))
);
// The curve F2 is obtained by replacing q by -q.
F2:=Curve(A2, -(-3*(t - 3)*(3*t + 1)*(t^2 - 6*t - 3) - 3*q*(3*t + 1)*(t^2 - 6*t + 3))*y^2
	+ x^3
	+ 3*(-q*(9*t^3 - 33*t^2 - 3*t - 1) - (9*t^4 - 60*t^3 + 42*t^2 + 44*t + 3))*x^2
	- 12*(-q*(3*t^3 + 13*t^2 - 33*t - 3) - t*(t + 6)*(3*t^2 - 14*t - 6))*x
	+ 12*(-q*(t - 3)*(t^2 - 6*t + 3) - (t^4 - 12*t^3 + 42*t^2 - 36*t - 9))
);
g1:=map<C->F1|[6 * (3*t + 1 + (t + 1 - q)*x)^2/(3*t + 1 + (t + 1 + q)*x)^2, 8*(3*t+1) * y/(3*t + 1 + (t + 1 + q)*x)^3]>;
g2:=map<C->F2|[6 * (3*t + 1 + (t + 1 + q)*x)^2/(3*t + 1 + (t + 1 - q)*x)^2, 8*(3*t+1) * y/(3*t + 1 + (t + 1 - q)*x)^3]>;

/* F1 and F2 are 9-isogenous. The kernel polynomial of the isogeny F1->F2 when t=-(s^2 + s + 1)/(2*s^2 + s) and q=(s^2+ 4*s + 1)/(2*s^2 + s)
   is given by
   x^8 - 96*(s^2 + 2*s + 3)*(s^3 - 7*s^2 - 6*s - 9)*(s^2 + 4*s + 1)/s^7 * x^7
       - 576*(s^2 + 2*s + 3)^2*(17*s^6 + 218*s^5 + 104*s^4 + 174*s^3 - 360*s^2 - 216*s - 324)*(s^2 + 4*s + 1)^2/s^14 * x^6
       + 124416*(s^2 + 2*s + 3)^3*(9*s^8 + 19*s^7 - 214*s^6 - 555*s^5 - 1336*s^4 - 1544*s^3 - 1644*s^2 - 864*s - 432)*(s^2 + 4*s + 1)^3/s^20 * x^5
       + 124416*(s^2 + 2*s + 3)^4*(49*s^10 + 5236*s^9 + 30880*s^8 + 77372*s^7 + 158096*s^6 + 203120*s^5 + 237480*s^4 + 183168*s^3 + 143424*s^2 + 62208*s + 31104)*(s^2 + 4*s + 1)^4/s^26 * x^4
       - 5971968*(s^2 + 2*s + 3)^5*(509*s^11 + 6441*s^10 + 23586*s^9 + 43607*s^8 + 48048*s^7 - 25008*s^6 - 140488*s^5 - 299712*s^4 - 337248*s^3 - 304128*s^2 - 155520*s - 62208)*(s^2 + 4*s + 1)^5/s^31 * x^3
       + 107495424*(s^2 + 2*s + 3)^6*(935*s^12 + 6914*s^11 + 13208*s^10 - 5434*s^9 - 92200*s^8 - 277912*s^7 - 448228*s^6 - 511360*s^5 - 300352*s^4 - 43776*s^3 + 183168*s^2 + 152064*s + 82944)*(s^2 + 4*s + 1)^6/s^36 * x^2
       - 2579890176*(s - 4)*(s + 2)*(s^2 + 2*s + 3)^7*(37*s^4 + 78*s^3 + 156*s^2 + 116*s + 72)*(13*s^6 + 47*s^5 + 30*s^4 - 7*s^3 - 176*s^2 - 168*s - 144)*(s^2 + 4*s + 1)^7/s^40 * x
       + (3869835264*(s - 4)^2*(s + 2)^2*(s^2 + 2*s + 3)^8*(37*s^4 + 78*s^3 + 156*s^2 + 116*s + 72)^2*(s^2 + 4*s + 1)^8)/s^44
*/

/***************************
 The family defined by Y1: To find a K-rational point and a suitable parametrization for Y1, we might have to extend the ground field.
 We first suppose that K is not of characeristic 3 and contains a primitive third root of unity w.
****************************/
R<X>:=PolynomialRing(QQ);
F<w>:=ext<QQ|X^2+X+1>;
PP<a,b,c>:=WeightedProjectiveSpace(F,[1,2,3]);
A1<t>:=AffineSpace(F,1);
Y1:=Scheme(PP, 16*a^6*b^6 - 864*a^6*b^3*c^2 + 11664*a^6*c^4 - 324*a^5*b^5*c + 8748*a^5*b^2*c^3 - 81*a^4*b^7 + 14580*a^4*b^4*c^2
              - 157464*a^4*b*c^4 - 864*a^3*b^6*c - 215784*a^3*b^3*c^3 + 78732*a^3*c^5 + 324*a^2*b^8 + 30618*a^2*b^5*c^2
              + 2125764*a^2*b^2*c^4 - 5832*a*b^7*c - 314928*a*b^4*c^3 - 6377292*a*b*c^5 + 37908*b^6*c^2 + 255879*b^3*c^4 + 8503056*c^6);

// a parametrization of Y1
p:=map<A1->Y1|[
   -3*w*(t^2 - w*t - 3*w^2)*(t^2 - 6*t - 3),
   48*t^2*(t^2 + 3*w*t - 3*w^2)*(t^2 - 6*t - 3),
   64*t^3*(t^2 + 3*t - 3)*(t^2 - 6*t - 3)^2
]>;

// for the representative obtained by rescaling by 1/(4*t*(t^2 - 6*t - 3)) we obtain the following family (and its twists):
K<t>:=FunctionField(F);
A2<x,y>:=AffineSpace(K,2);
C:=Curve(A2, -y^2 + (4*t*(t^2 - 6*t - 3)*x^3 - 3*w*(t^2 - 6*t - 3)*(t^2 - w*t - 3*w^2)*x^2 + 12*t*(t^2 + 3*w*t - 3*w^2)*x + 4*t*(t^2 + 3*t - 3)) * (4*(t^2 - 6*t - 3)*(t^2 + 3*t - 3)*x^3 + 9*(t^2 + 3*w*t - 3*w^2)^2*x^2 + 6*(t^2 + 3*t - 3)*(t^2 + 3*w*t - 3*w^2)*x + (t^2 + 3*t - 3)^2));
E1:=Curve(A2, -t*(t^2 - 6*t - 3)*y^2 + x^3 + 3*(t^2 + t*(1 - w) + 3*w)/(t^2 - t*(1 - w^2) + 3*w^2)*x^2 + 3*(t^6 - 2*(2 + w)*t^5 - 3*t^4*(5 - 2*w) + 18*t^3*w - 9*t^2*(5 + 7*w) + 18*t*(2 + w) + 27*(1 + w))/((t^2 - 6*t - 3)*(t^2 - t*(1 - w^2) + 3*w^2)^2)*x + (t^2 + 3*t - 3)/(t^2 - 6*t - 3));
E2:=Curve(A2, -t*(t^2 - 6*t - 3)*(t^2 + (w^2 - 1)*t + 3*w^2)*y^2 + x^3 + 3*(t^2 - (w^2 - 1)*t + 3*w^2)*x^2 + ((3*(t^6 - 2*(2 + w^2)*t^5 - 3*(5 - 2*w^2)*t^4 + 18*t^3*w^2 - 9*(5 + 7*w^2)*t^2 + 18*(2 + w^2)*t + 27*(1 + w^2)))/(t^2 - 6*t - 3))*x + (t^2 + (w - 1)*t + 3*w)^3*((t^2 + 3*t - 3)/(t^2 - 6*t - 3)));

// complementary degree-3 maps
f1:=map<C->E1|[
  3*w*(t^2 + (w^2 - 1)*t + 3*w^2)^2 * x^2/(4*t*(t^2 - 6*t - 3)*x^3 - 3*w*(t^2 - 6*t - 3)*(t^2 - w*t - 3*w^2)*x^2 + 12*t*(t^2 + 3*w*t - 3*w^2)*x + 4*t*(t^2 + 3*t - 3)),
  4*t/(t^2 - 6*t - 3) * y*((t^2 - 6*t - 3)*x^3 - 3*x*(t^2 + 3*t*w - 3*w^2) - 2*(t^2 + 3*t - 3))/(4*t*(t^2 - 6*t - 3)*x^3 - 3*w*(t^2 - 6*t - 3)*(t^2 - w*t - 3*w^2)*x^2 + 12*t*(t^2 + 3*w*t - 3*w^2)*x + 4*t*(t^2 + 3*t - 3))^2
]>;
f2:=map<C->E2|[
 -1/(t^2 + (w^2 - 1)*t + 3*w^2) * ((t^2 + 3*t*w - 3*w^2)*x + t^2 + 3*t - 3)^2*(4*(t^4 - 3*t^3 + 3*t^2 + 9*t + 9)*x + (t^2 + 3*t - 3)*(t^2 + 3*w^2*t - 3*w))/(4*(t^2 - 6*t - 3)*(t^2 + 3*t - 3)*x^3 + 9*(t^2 + 3*w*t - 3*w^2)^2*x^2 + 6*(t^2 + 3*t - 3)*(t^2 + 3*w*t - 3*w^2)*x + (t^2 + 3*t - 3)^2),
 12*(1 + 2*w)*t/((t^2 + (w^2 - 1)*t + 3*w^2)^2*(t^2 - 6*t - 3)) * y*(3*w*(t^2 + 3*t - 3)*(t^3 - 3*t^2 - 3*t*(4 + 3*w) - 9*w)*(t^3 - (3 + 4*w)*t^2 + 3*w*t + 3*w)*x^2 + x^3*(9*t^8*w - 45*t^7*w + 81*t^6*w - 27*t^5*w - 81*t^3*w - 729*t^2*w + 17*t^7 - 27*t^6 - 99*t^5 + 540*t^4 + 216*t^3 - 972*t^2 - 1215*t*w - 1674*t - 729*w - 729) - 3*t*(t^2 + 3*t - 3)^2*x*(t^2 + 3*t*w + 3*w + 3) - t*(t^2 + 3*t - 3)^3)/(4*(t^2 - 6*t - 3)*(t^2 + 3*t - 3)*x^3 + 9*(t^2 + 3*w*t - 3*w^2)^2*x^2 + 6*(t^2 + 3*t - 3)*(t^2 + 3*w*t - 3*w^2)*x + (t^2 + 3*t - 3)^2)^2
]>;

// an isomorphism between the two elliptic curves
iso:=map<E1->E2|[ w^2*(t^2 + (w^2-1)*t + 3*w^2)*x - (w+2)*(t-1)*(t+3), (t^2 + (w^2-1)*t + 3*w^2)*y ]>;

R<X>:=PolynomialRing(K);
h:=hom<Parent(x)->R | [X,0] >;
j:=jInvariant(EllipticCurve(h(Basis(Ideal(E1))[1])));
j eq 27*(t - 3)^3*(t + 1)^3/t^3;
// note that this is the same formula in terms of t as the one we obtained for the curves parametrized by X1


/********************************************
 The case of base field of characteristic 3.
*********************************************/
/* In this case the curve C is singular if b=0 so we have the following two curves parametrizing the two kinds of curves C considered above:
   X1: a^3*c + 2*a^2*b^2 + 2*b^3=0
   Y1: a=0
   A parametrization of X1 is given by t |--> [t:t:t+1].
   A parametrization of Y1 is given by t |--> [0:t:1].  */

/* First we consider the family parametrized by X1, i.e. curves C with a degree-3 map C->E such that the complementary covering is
   obtained by pre-composing with an involution of C. This can all be obtained by everything reducing modulo 3 in the family defined
   by X1 in the general case. */
K<t>:=FunctionField(GF(3));
A2<x,y>:=AffineSpace(K,2);
C:=Curve(A2, -y^2 + (x^3 + t*x^2 + t*x + t + 1)*((t + 1)*x^3 + t^2*x^2 - t*(t + 1)*x + (t + 1)^2));
E:=Curve(A2, -y^2 + x^3 + t*x^2 + t*x + t + 1);
f1:=map<C->E|[
	t*x^2/(x^3 + t*x^2 + t*x + t + 1),
	((x^3 - t*x + t + 1)*y)/(x^3 + t*x^2 + t*x + t + 1)^2
]>;
f2:=map<C->E|[
	-((t*x^2*(x - t - 1))/((t + 1)*x^3 + t^2*x^2 - t*(t + 1)*x + (t + 1)^2)),
	(((t^2 + t - 1)*x^3 - t*(1 + t)*x^2 - t*(t + 1)^2*x - (t + 1)^3)*y)/((t + 1)*x^3 + t^2*x^2 - t*(t + 1)*x + (t + 1)^2)^2
]>;

// an involution on C, such that f2 = f1∘inv
inv:=map<C->C|[ ((t + 1)*x)/(x - t - 1), y*(t + 1)^3/(x - t - 1)^3 ]>;

R<X>:=PolynomialRing(K);
h:=hom<CoordinateRing(A2)->R | [X,0]>;
j:=jInvariant(EllipticCurve(h(Basis(Ideal(E))[1])));
j eq t^3;

/* The family parametrized by Y1 behaves differently in characteristic 3 */
C:=Curve(A2, -y^2 + (x^3 + t*x + 1)*(x^3 + t^2*x^2 - t*x + 1));
E1:=Curve(A2, -y^2 + x^3 - t*x + 1);
E2:=Curve(A2, -y^2 + x^3 + t*x + 1);
f1:=map<C->E1|[-t*x^2/(x^3 + t*x + 1), y*(x^3 - t*x + 1)/(x^3 + t*x + 1)^2]>;
f2:=map<C->E2|[(t*x^2*(t*x + 1))/(x^3 + t^2*x^2 - t*x + 1), y*((t - 1)^3*x^3 + t^2*x^2 - t*x - 1)/(x^3 + t^2*x^2 - t*x + 1)^2]>;
R<X>:=PolynomialRing(K);
h:=hom<CoordinateRing(A2)->R | [X,0]>;
j:=jInvariant(EllipticCurve(h(Basis(Ideal(E1))[1])));
j eq 0;

/* The curve y^2 =  (x^3 + t*x + 1)*(x^3 + t^2*x^2 - t*x + 1) = P(x)*Q(x) does not have additional involutions
   (but it could have automorphisms of order >2). */
K<p,q,r,t>:=FunctionField(GF(3),4);
R<x,y>:=PolynomialRing(K,2);
P:=func<x | x^3 + t*x + 1 >;
Q:=func<x | x^3 + t^2*x^2 - t*x + 1 >;
res:=Resultant((r*y-p)*x - (p*y+q), P(y)*Q(y), y);
_,rem:=Quotrem(res, P(x)*Q(x));
eqns:=[Coefficient(rem,x,k) : k in [0..5]];
R<z,p,q,r,t>:=PolynomialRing(GF(3),5);
h:=hom<K->R|[p,q,r,t]>;
eqns:=[h(g) : g in eqns] cat [1-z*(p^2+q*r)*t];
I:=ideal<R | eqns >;
J:=Radical(EliminationIdeal(I,4));
J;
