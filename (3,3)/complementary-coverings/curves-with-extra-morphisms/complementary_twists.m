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
K<w>:=ext<QQ|X^2+X+1>;
PP<a,b,c>:=WeightedProjectiveSpace(K,[1,2,3]);
A1<t>:=AffineSpace(K,1);
Y1:=Scheme(PP, 16*a^6*b^6 - 864*a^6*b^3*c^2 + 11664*a^6*c^4 - 324*a^5*b^5*c + 8748*a^5*b^2*c^3 - 81*a^4*b^7 + 14580*a^4*b^4*c^2
              - 157464*a^4*b*c^4 - 864*a^3*b^6*c - 215784*a^3*b^3*c^3 + 78732*a^3*c^5 + 324*a^2*b^8 + 30618*a^2*b^5*c^2
              + 2125764*a^2*b^2*c^4 - 5832*a*b^7*c - 314928*a*b^4*c^3 - 6377292*a*b*c^5 + 37908*b^6*c^2 + 255879*b^3*c^4 + 8503056*c^6);

// a parametrization of Y1
p:=map<A1->Y1|[-3*w*(t^2 - w*t - 3*w^2)*(t^2 - 6*t - 3), 48*t^2*(t^2 + 3*w*t - 3*w^2)*(t^2 - 6*t - 3), 64*t^3*(t^2 + 3*t - 3)*(t^2 - 6*t - 3)^2]>;

