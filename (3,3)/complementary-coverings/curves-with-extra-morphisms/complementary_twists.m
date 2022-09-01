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
p:=map<A1->X1|[(t-3)*(t-9), -16*(t-3)*t^2, 64*(t-1)*t^3]>;  // t |--> [-3*(t-3), -6*(t-2)*t^2, 2*(t+1)*(t-2)^2*t^3] also works but not in characteristic 3

// This choice leads to the following choice of parametrizations of the curves (with the obvious modifications for their quadratic twists).
K<t>:=FunctionField(QQ);
A2<x,y>:=AffineSpace(K,2);
C:=Curve(A2, -y^2 + (4*t*x^3 + (t - 9)*(t - 3)*x^2 - 4*(t - 3)*t*x + 4*t*(t - 1))*(4*(t - 1)*x^3 + (t - 3)^2*x^2 - 2*(t - 3)*(t - 1)*x + (t - 1)^2));
E1:=Curve(A2, -y^2 + x^3 + (t - 3)/t*x^2 + (t - 3)*(2*t^2 - 27*t + 27)/(t^2*(t^2 + 18*t - 27))*x + (t -1)/t^3);
E2:=Curve(A2, -(t^2 + 18*t - 27)*y^2 + x^3 + (t - 3)/t*x^2 + (t - 3)*(2*t^2 - 27*t + 27)/(t^2*(t^2 + 18*t - 27))*x + (t - 1)/t^3);
// note that E1 and E2 are clearly twists of each other

f1:=map<C->E1|[
  -(t^2 + 18*t - 27)/t * x^2/(4*t*x^3 + (t - 9)*(t - 3)*x^2 - 4*(t - 3)*t*x + 4*t*(t - 1)),
  4 * y*(x^3 + (t - 3)*x - 2*(t - 1))/(4*t*x^3 + (t - 9)*(t - 3)*x^2 - 4*(t - 3)*t*x + 4*t*(t - 1))^2
]>;
f2:=map<C->E2|[
  -1/(t^2 + 18*t - 27)/t * ((t - 3)*x - 3*(t - 1))^2*(4*(2*t - 3)*x + (t - 3)*(t - 1))/(4*(t - 1)*x^3 + (t - 3)^2*x^2 - 2*(t - 3)*(t - 1)*x + (t - 1)^2), 
  4/(t^2 + 18*t - 27)^2 * y*((t^3 + 35*t^2 - 109*t + 81)*x^3 + (t - 3)*(t - 1)*(7*t - 9)*x^2 + t*(t - 3)*(t - 1)^2*x - t*(t - 1)^3)/(4*(t - 1)*x^3 + (t - 3)^2*x^2 - 2*(t - 3)*(t - 1)*x + (t - 1)^2)^2
]>;

R<X>:=PolynomialRing(K);
h:=hom<CoordinateRing(A2)->R | [X,0]>;
j:=jInvariant(EllipticCurve(h(Basis(Ideal(E1))[1])));
j eq -(t - 3)^3*(t + 9)^3/t^3;

// After extending K if necessary, C admits a non-hyperelliptic involution and E1 and E2 are isomorphic, via (x,y) |--> (x,q*y).
R<X>:=PolynomialRing(K);
K<q>:=ext<K|X^2 - (t^2 + 18*t - 27)>;
A2<x,y>:=AffineSpace(K,2);
C:=Curve(A2, -y^2 + (4*t*x^3 + (t - 9)*(t - 3)*x^2 - 4*(t - 3)*t*x + 4*t*(t - 1))*(4*(t - 1)*x^3 + (t - 3)^2*x^2 - 2*(t - 3)*(t - 1)*x + (t - 1)^2));

// an involution on C
inv:=map<C->C|[
  -(t - 1)*((t - 3)*x - 3*(t - 1))/(4*(2*t - 3)*x + (t - 3)*(t - 1)),
  y*(q*(t - 1)/(4*(2*t - 3)*x + (t - 3)*(t - 1)))^3
]>;

// The composition f1∘inv is the same map as f2 post-composed with the isomorphism (x,y) |--> (x,q*y).


/***************************
 The family defined by Y1. To find a K-rational point and a suitable parametrization for Y1, we might have to extend the ground field.
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
   -w*(t^2 + 3*t*w - 27*w^2)*(t^2 + 18*t - 27),
   48*t^2*(t^2 - 9*t*w - 27*w^2)*(t^2 + 18*t - 27),
   -64*t^3*(t^2 - 9*t - 27)*(t^2 + 18*t - 27)^2
]>;
/* also good is: t |--> [-3*w*(t^2 - w*t - 3*w^2)*(t^2 - 6*t - 3), 48*t^2*(t^2 + 3*w*t - 3*w^2)*(t^2 - 6*t - 3), 64*t^3*(t^2 + 3*t - 3)*(t^2 - 6*t - 3)^2],
   but we are aiming for a specific j-invariant */

// for the representative obtained by rescaling by 1/(4*t*(t^2+ 18 t - 27)) we obtain the following family (up to twists):
K<t>:=FunctionField(F);
A2<x,y>:=AffineSpace(K,2);
C:=Curve(A2, -y^2 + (4*t*(t^2 + 18*t - 27)*x^3 - w*(t^2 + 18*t - 27)*(t^2 + 3*t*w - 27*w^2)*x^2 + 12*t*(t^2 - 9*t*w - 27*w^2)*x - 4*t*(t^2 - 9*t - 27))*(-4*(t^2 - 9*t - 27)*(t^2 + 18*t - 27)*x^3 + 9*(t^2 - 9*t*w - 27*w^2)^2*x^2 - 6*(t^2 - 9*t - 27)*(t^2 - 9*t*w - 27*w^2)*x + (t^2 - 9*t - 27)^2));
E1:=Curve(A2, -t/(t^2 + 18*t - 27)*y^2 + x^3 + (-3*t^2 + (-9*w + 9)*t - 81*w)/(t^2 + (3*w + 6)*t - 27*w - 27)*x^2 + (3*t^6 + (18*w + 36)*t^5 + (162*w - 405)*t^4 - 1458*w*t^3 + (-15309*w - 10935)*t^2 + (-13122*w - 26244)*t + 59049*w + 59049)/(t^6 + (6*w + 30)*t^5 + (81*w + 162)*t^4 + (-972*w - 972)*t^3 + (-4374*w - 2187)*t^2 + (21870*w + 4374)*t - 19683*w)*x + (-t^2 + 9*t + 27)/(t^2 + 18*t - 27));
E2:=Curve(A2, -t*(t^2 + (3*w + 6)*t + 27*w^2)*y^2/(t^2 + 18*t - 27) + x^3 - 3*(t^2 - (3*w + 6)*t + 27*w^2)*x^2 + (3/(t^2 + 18*t - 27))*(t^6 + (-6*w + 6)*t^5 + (-54*w - 189)*t^4 + (486*w + 486)*t^3 + (5103*w + 1458)*t^2 + (4374*w - 4374)*t - 19683*w)*x - (1/(t^2 + 18*t - 27))*(t^2 - 9*t - 27)*(t^2 + (-3*w + 3)*t + 27*w)^3);

// complementary degree-3 maps
f1:=map<C->E1|[
	-w*(t^2 + (3*w + 6)*t + 27*w^2)^2*x^2/(4*t*(t^2 + 18*t - 27)*x^3 - w*(t^2 + 18*t - 27)*(t^2 + 3*t*w - 27*w^2)*x^2 + 12*t*(t^2 - 9*t*w - 27*w^2)*x - 4*t*(t^2 - 9*t - 27)), 
	4*t*((t^2 + 18*t - 27)*x^3 - 3*x*(t^2 - 9*t*w - 27*w^2) + 2*(t^2 - 9*t - 27))*y/(4*t*(t^2 + 18*t - 27)*x^3 - w*(t^2 + 18*t - 27)*(t^2 + 3*t*w - 27*w^2)*x^2 + 12*t*(t^2 - 9*t*w - 27*w^2)*x - 4*t*(t^2 - 9*t - 27))^2
]>;
f2:=map<C->E2|[
	-1/(t^2 + (3*w + 6)*t + 27*w^2)*((t^2 - 9*w*t + 27*w + 27)*x - (t^2 - 9*t - 27))^2*(4*(t^2 - 9*w*t - 27)*(t^2 - 9*w^2*t - 27)*x - (t^2 - 9*t - 27)*(t^2 - 9*w^2*t - 27*w))/(-4*(t^2 - 9*t - 27)*(t^2 + 18*t - 27)*x^3 + 9*(t^2 - 9*t*w - 27*w^2)^2*x^2 - 6*(t^2 - 9*t - 27)*(t^2 - 9*t*w - 27*w^2)*x + (t^2 - 9*t - 27)^2), 
	(1+2*w)*4*81*t/(t^2 + (3*w + 6)*t + 27*w^2)^2 * (x^3*(3*t^8*w + t^7*(45*w - 17) + t^6*(243*w - 81) + t^5*(243*w + 891) + t^3*(6561*w - 17496) + t^2*(-(177147*w) - 236196) + 14580*t^4 + t*(885735*w + 1220346) - 1594323*w - 1594323) - w*(t^2 - 9*t - 27)*(t^3 + 9*t^2 + t*(-(81*w) - 108) + 243*w)*(t^2*(12*w + 9) + t^3 + 27*t*w - 81*w)*x^2 + 3*t*(t^2 - 9*t - 27)^2*(t^2 - 9*t*w + 27*w + 27)*x - t*(t^2 - 9*t - 27)^3)*y/(-4*(t^2 - 9*t - 27)*(t^2 + 18*t - 27)*x^3 + 9*(t^2 - 9*t*w - 27*w^2)^2*x^2 - 6*(t^2 - 9*t - 27)*(t^2 - 9*t*w - 27*w^2)*x + (t^2 - 9*t - 27)^2)^2
]>;

// an isomorphism between the two elliptic curves
iso:=map<E1->E2|[ w^2*(t^2 + (3*w + 6)*t + 27*w^2)*x + (1 - w^2)*(t - 9)*(t + 3), (t^2 + (3*w + 6)*t + 27*w^2)*y ]>;

R<X>:=PolynomialRing(K);
h:=hom<Parent(x)->R | [X,0] >;
j:=jInvariant(EllipticCurve(h(Basis(Ideal(E1))[1])));
j eq -(t - 3)^3*(t + 9)^3/t^3;
// note that this is the same formula in terms of t as the one we obtained for the curves parametrized by X1


/********************************************
 The case of base field of characteristic 3.
 In this case the curve C is singular if b=0 so we have the following two curves parametrizing the two kinds of curves C considered above:
 X1: a^3*c + 2*a^2*b^2 + 2*b^3=0
 Y1: a=0
 A parametrization of X1 is given by t |--> [t:-t:t-1]  or  [t:t:t+1] after replacing t by -t.
 A parametrization of Y1 is given by t |--> [0:t:1]
*********************************************/



