/***********************************/
/********** Example 3.2 ************/
/***********************************/
R<x>:=PolynomialRing(QQ);
K<q,r>:=NumberField([x^3-4, x^2+3]);
R<x>:=PolynomialRing(K);
C:=HyperellipticCurve((x^3+1)*(4*x^3+1));

// these curves are isogenous; F1 and F2 are 9-isogenous over Q, and E1,E2,F2 are isomorphic over Q(q,r)
E1:=EllipticCurve(x^3+4);
E2:=EllipticCurve(x^3+1);
F1:=EllipticCurve(x^3 + 150*x^2 - 180*x + 72);
F2:=EllipticCurve(x^3 + 90*x^2 + 2700*x - 648);
L<x,y>:=FunctionField(C);

// degree-3 coverings
f1:=map<C->E1 | [-3*x^2/(x^3+1), y*(x^3-2)/(x^3+1)^2, 1]>;
f2:=map<C->E2 | [-3*x/(4*x^3+1), y*(8*x^3-1)/(4*x^3+1)^2, 1]>;

// degree-2 coverings
g1:=map<C->F1 | [-2*(2*x-q)^2/(2*x+q)^2, 128*y/(2*x+q)^3, 1]>;
g2:=map<C->F2 | [18*(2*x + q)^2/(2*x - q)^2, 1152*y/(2*x - q)^3, 1]>; 
inv:=map<C->C | [1/(q*x), -y/(2*x^3), 1]>;

L<x,y>:=FunctionField(E2);
iso1:=map<E2->E1 | [q*x, 2*y, 1]>;
iso2:=map<E2->F2 | [-12*q^2*x - 30, 96*r*y, 1]>;



/***********************************/
/********** Example 3.3 ************/
/***********************************/
R<x>:=PolynomialRing(QQ);
K<r>:=NumberField(x^2+3);
R<x>:=PolynomialRing(K);
C:=HyperellipticCurve((x^3 + 6*x^2 + 12*x + 10)*(10*x^3 + 36*x^2 + 60*x + 25));
E1:=EllipticCurve(x^3 + 12*x^2 + 48*x + 10);
E2:=EllipticCurve(x^3 - 36*x^2 + 432*x - 270);
L<x,y>:=FunctionField(C);
f1:=map<C->E1 | [-3*x^2/(x^3 + 6*x^2 + 12*x + 10), y*(x^3 - 12*x - 20)/(x^3 + 6*x^2 + 12*x + 10)^2, 1]>;
f2:=map<C->E2 | [-3*(2*x + 5)^2*(7*x + 10)/(10*x^3 + 36*x^2 + 60*x + 25), 27*y*(44*x^3 + 120*x^2 + 150*x + 125)/(10*x^3 + 36*x^2 + 60*x + 25)^2, 1]>;
inv:=map<C->C | [-5*(2*x+5)/(7*x+10), y*375*r/(7*x+10)^3, 1]>;

// the 2-coverings induced by the extra involution
R<x>:=PolynomialRing(K);
F1:=EllipticCurve(x^3 + 1/2*(15*r + 3795)*x^2 + 1/2*(18975*r + 225)*x + 375*r);
F2:=EllipticCurve(x^3 + 1/2*(-15*r + 3795)*x^2 + 1/2*(-18975*r + 225)*x - 375*r);
L<x,y>:=FunctionField(C);
g1:=map<C->F1|[5*r*(11 - 5*r)/98 * ((7*x + 10 - 5*r)/((2 - r)*x + 5))^2, 2^3*3*5^3*y/((2 - r)*x + 5)^3, 1]>;
g2:=map<C->F2|[-5*r*(5*r + 11)/2 * ((2-r)*x + 5)^2/(7*x + 10 - 5*r)^2,   2^3*3*5^3*(9*r + 10) * y/(7*x + 10 - 5*r)^3, 1]>;
_,f:=IsIsomorphic(F1,F2);
f;

// there is a separable 3-isogeny E1 --> F1 over K(r), which we can write as a composition of a 3-isogeny E1-->F over K and an isomorphism F-->F1 over K(r)
R<x>:=PolynomialRing(K);
F:=EllipticCurve(x^3 + 12*x^2 - 1032*x - 17918);
L<x,y>:=FunctionField(E1);
isog3:=map<E1->F|[(x^3 - 4*x^2 + 220*x + 216) / (x^2 - 4*x + 4),  (x^3*y - 6*x^2*y - 204*x*y - 872*y) / (x^3 - 6*x^2 + 12*x - 8), 1]>;
_,f:=IsIsomorphic(F,F1);
f;


/***********************************/
/********** Example 3.6 ************/
/***********************************/
R<x>:=PolynomialRing(Rationals());
K<q>:=NumberField(x^4-3/4);
R<x>:=PolynomialRing(K);
C:=HyperellipticCurve(x*(x^2 + 1)*(4*x^2 + 3));
E1:=EllipticCurve(x^3 + x);
E2:=EllipticCurve(x^3 + 108*x);
L<x,y>:=FunctionField(C);
f1:=map<C->E1 | [1/(x*(4*x^2 + 3)), y*(4*x^2 + 1)/(x^2*(4*x^2 + 3)^2), 1] >;
f2:=map<C->E2 | [4*x^3/(x^2 + 1), y*4*x*(x^2 + 3)/(x^2 + 1)^2, 1] >;
inv:=map<C->C | [q^2/x, q^3*y/x^3 , 1]>;

 
// induced degree-2 coverings
P2<X,Y,Z>:=ProjectiveSpace(K,2);
iso:=map<C->P2 | [(-3 - 4*q - 4*q^2 - 4*q^3 + 4*(1 + q)*(1 + q^2)*x)/(-3 + 4*q - 4*q^2 + 4*q^3 + 4*(1 - q)*(1 + q^2)*x),
                   8*q*(1 + q^2)*y/(-3 + 4*q - 4*q^2 + 4*q^3 + 4*(1 - q)*(1 + q^2)*x)^3,
                   1 ]>;
g1:=map<P2->P2 | [X^2, Y*Z, Z^2]>;
g2:=map<P2->P2 | [X*Z^2, Y*Z^2, X^3]>;
F1:=g1(iso(C)); F1:=EllipticCurve(F1,F1![0,1,0]);
F2:=g2(iso(C)); F2:=EllipticCurve(F2,F2![0,1,0]);
jInvariant(F1);
jInvariant(F2);



/***********************************/
/********** Example 3.7 ************/
/***********************************/
R<x>:=PolynomialRing(Rationals());
C:=HyperellipticCurve(x*(2*x^2 + 4*x + 3)*(3*x^2 + 4*x + 2));
E1:=EllipticCurve(x*(x^2 + 44*x + 486));
E2:=EllipticCurve(x^3 - x^2 + x + 3);
L<x,y>:=FunctionField(C);
inv:=map<C->C | [1/x, y/x^3,1]>;
f1:=map<C->E1 | [18*x^3/(3*x^2 + 4*x + 2), y*18*x*(3*x^2 + 8*x + 6)/(3*x^2 + 4*x + 2)^2, 1]>;
g1:=map<C->E1 | [18/(x*(2*x^2 + 4*x + 3)), y*18*(6*x^2 + 8*x + 3)/(x*(2*x^2 + 4*x + 3))^2, 1]>; // this is f1∘inv, but it is NOT f2, in spite of the correct denominator
f2:=map<C->E2 | [(-2*x^3 + 4*x^2 + 5*x + 2)/(x*(2*x^2 + 4*x + 3)), y*2*(2*x+1)*(2*x^2+1)/(x^2*(2*x^2 + 4*x + 3)^2), 1]>; // this is f2
g2:=map<C->E2 | [(2*x^3 + 5*x^2 + 4*x - 2)/(3*x^2 + 4*x + 2), y*2*(x+2)*(x^2+2)/(3*x^2 + 4*x + 2)^2, 1]>; // this is f2∘inv


/***********************************/
/********** Example 3.8 ************/
/***********************************/
// the only case where j(E)=0 and C-->E has a single ramification point
K:=Rationals();
R<x>:=PolynomialRing(K);
C:=HyperellipticCurve((x+2)*(x^2+x+1)*(8*x^3 + 9*x^2 + 12*x + 4));
E1:=EllipticCurve(x^3 + 6*x^2 + 21*x + 8);
E2:=EllipticCurve(x*(x^2 - 3*x + 3));
L<x,y>:=FunctionField(C);
f1:=map<C->E1 | [-3*x^2/((x+2)*(x^2+x+1)), y*(x^3-3*x-4)/((x+2)*(x^2+x+1))^2, 1]>;
f2:=map<C->E2 | [(x+2)^3/(8*x^3 + 9*x^2 + 12*x + 4), y*(x+2)*(13*x^2 + 4*x + 4)/(8*x^3 + 9*x^2 + 12*x + 4)^2, 1]>; //triply ramified at x=-2
[jInvariant(E1), jInvariant(E2)];



/***********************************/
/********** Example 3.9 ************/
/***********************************/
// the only case where j(E1)=j(E2) and C-->E2 has a single ramification point and C-->E1 has two ramification points
QQ:=Rationals();
R<x>:=PolynomialRing(QQ);
K<q>:=NumberField(x^2+15);
R<x>:=PolynomialRing(K);
P:=func<x | ((1+q)*x-32)*(4*x^2 - (7-q)*x - 8*(1+q))>;
Q:=func<x | 32*x^3 - 9*(7-q)*x^2 - 96*(1 +q)*x + 512>;
R:=func<x | (1+q)*x^3 - 12*(7 - q)*x - 128*(1 + q)>;
S:=func<x | ((1+q)*x-32)*((479-9*q)*x^2 - 32*(7 - q)*x - 256*(1+q))>;
C:=HyperellipticCurve(P(x)*Q(x));
E1:=EllipticCurve(x^3 - 4*x^2 + (19+q)/3*x - 64/27);
E2:=EllipticCurve(x^3 + (3-q)*x^2 - (3+5*q)/3*x);
L<x,y>:=FunctionField(E1);
iso:=map<E1->E2 | [x-(7-q)/3, y, 1]>;
L<x,y>:=FunctionField(C);
f1:=map<C->E1 | [(-156+4*q)*x^2/P(x), 8*(3-q)/9*R(x)/P(x)^2*y, 1]>;
f2:=map<C->E2 | [(11-3*q)/384*((1+q)*x - 32)^3/Q(x), 2*(27-19*q)/9216*S(x)/Q(x)^2*y, 1]>; 
[jInvariant(E1), jInvariant(E2)];
