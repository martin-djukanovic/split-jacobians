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
   such that E1 and E2 are twists (resp. 5-isogenous, resp. 8-isogenous). */


/* The family defined by X5 is also precisely the family determined by the second primary component of the final elimination ideal computed
   when analysing the generic case. This is verified by the following: */
RR<x,y,z,d,e,a,b,c> := PolynomialRing(QQ,8);
P := func<u | u^3 + a*u^2 + b*u + c >;
D := func<u | u*Derivative(P(u),u) - 2*P(u)>;
Q := func<u | Quotrem(Resultant(u^2*P(z) - z^2*P(u), D(z), z), Resultant(u,P(u),u)*D(u)^2) >;
D2 := func<u | (u+e)*(u+d)*Derivative(Q(u),u) - Q(u)*(2*(u+e) + (u+d)) >;
R := Resultant((x+d)^2*(x+e)*Q(y) - (y+d)^2*(y+e)*Q(x), D2(y), y);
R := Quotrem(R, Resultant((x+d)*(x+e),Q(x),x)*D2(x)^2);
q,r := Quotrem(R,P(x));
I := ideal< RR | [
  Coefficient(r,x,0), Coefficient(r,x,1), Coefficient(r,x,2),
  1 - z * Resultant((x+d)*(x+e),Q(x),x) * Resultant(x,P(x),x) * Discriminant(P(x),x) * Discriminant(Q(x),x) * Resultant(x+d,x+e,x)
]>;
J := PrimaryDecomposition(EliminationIdeal(I,3))[2];
Basis(EliminationIdeal(J,5))[1];


/* The curve X1 does not cover all the cases with j(E1)=j(E2). By equating the formulas for the j-invariants of E1 and E2 obtained in
   the generic case, we find that there is another 1-dimensional family of such curves C. */
R<j1,j2,a,b,c>:=PolynomialRing(QQ,5);
I:=ideal<R|[
 j1*(b^3 - 27*c^2)^3*(a^2*b^2 - 4*b^3 - 4*a^3*c + 18*a*b*c - 27*c^2)^2 - 16*(a^2*b^4 + 12*b^5 - 126*a*b^3*c + 216*a^2*b*c^2 + 405*b^2*c^2 - 972*a*c^3)^3,
 j2*(a^2*b^2 - 4*a^3*c + 18*a*b*c - 4*b^3 - 27*c^2) - 256*(a^2 - 3*b)^3,
 j1 - j2
]>;
J:=EliminationIdeal(I,2);
PrimaryDecomposition(J);

/*  The equations define a union of X1 and another genus-0 curve, namely
    Y1: 16*a^6*b^6 - 864*a^6*b^3*c^2 + 11664*a^6*c^4 - 324*a^5*b^5*c + 8748*a^5*b^2*c^3 - 81*a^4*b^7 + 14580*a^4*b^4*c^2 - 157464*a^4*b*c^4 - 864*a^3*b^6*c -
    215784*a^3*b^3*c^3 + 78732*a^3*c^5 + 324*a^2*b^8 + 30618*a^2*b^5*c^2 + 2125764*a^2*b^2*c^4 - 5832*a*b^7*c - 314928*a*b^4*c^3 - 6377292*a*b*c^5 +
    37908*b^6*c^2 + 255879*b^3*c^4 + 8503056*c^6 = 0
    
    In characteristic 3, Y1 reduces to a*b=0. However, C is then singular if b=0, so we can assume that b is non-zero so that Y1 is defined
    by a=0. Similarly, in characteristic 3 we can take X1: 2*a^2*b^2 + 2*b^3 + a^3*c=0.
    
    The genus-2 curves parametrized by X1,Y1,X5,X8 are further analysed in the other three files of the directory. The curves C defined by X1
    have additional involutions (after extending K if necessary) such that pre-composing a degree-3 map C->E with such an involution gives
    a complementary covering C->E. The curves defined by Y1 do not have this property, except for the three points of intersection with X1,
    which define curves C that cover a pair of elliptic curves with j(E)=0 or j(E)=1728. We verify this below.
*/

R<x>:=PolynomialRing(QQ);
K<i,w,u>:=ext<QQ|[x^2+1, x^2+x+1, x^2+19]>;  // not all such curves are defined over QQ (but their invariants are)
F<p,q,r,a,b,c>:=FunctionField(K,6);
R<x,y>:=PolynomialRing(F,2);
P:=func<x | x^3 + a*x^2 + b*x + c >;
Q:=func<x | 4*c*x^3 + b^2*x^2 + 2*b*c*x + c^2 >;

/* We look for curves C:y^2=P(x)Q(x) such that there exists a fractional linear transformation M(x)=(p*x+q)/(r*x-p) that sends the roots
of P(x) to the roots of Q(x) and vice versa. Such curves could potentially have complementary degree-3 maps to elliptic curves that are
obtained from one another by pre-composing with the involution. */
res1:=Resultant((r*y-p)*x - (p*y+q), P(y), y);
res2:=Resultant((r*y-p)*x - (p*y+q), Q(y), y);
_,rem1:=Quotrem(res1, Q(x));
_,rem2:=Quotrem(res2, P(x));
rem1:=rem1*4*c;
eqns:=[Coefficient(rem1,x,k) : k in [0..2]] cat [Coefficient(rem2,x,k) : k in [0..2]];
R<z,p,q,r,a,b,c>:=PolynomialRing(K,7);
h:=hom<F->R|[p,q,r,a,b,c]>;
eqns:=[h(g) : g in eqns] cat [
   // the equation of Y1
   16*a^6*b^6 - 864*a^6*b^3*c^2 + 11664*a^6*c^4 - 324*a^5*b^5*c + 8748*a^5*b^2*c^3 - 81*a^4*b^7 + 14580*a^4*b^4*c^2
     - 157464*a^4*b*c^4 - 864*a^3*b^6*c - 215784*a^3*b^3*c^3 + 78732*a^3*c^5 + 324*a^2*b^8 + 30618*a^2*b^5*c^2
     + 2125764*a^2*b^2*c^4 - 5832*a*b^7*c - 314928*a*b^4*c^3 - 6377292*a*b*c^5 + 37908*b^6*c^2 + 255879*b^3*c^4 + 8503056*c^6,
   // the equation that guarantees that the Disc(P(x)Q(x)) and Det(M) are non-zero
   1 - z*(p^2+q*r)*c*(b^3 - 27*c^2)*(-a^2*b^2 + 4*b^3 + 4*a^3*c - 18*a*b*c + 27*c^2)];
I:=ideal<R | eqns >;
J:=Radical(EliminationIdeal(I,4));

PP<a,b,c>:=WeightedProjectiveSpace(K,[1,2,3]);
h:=hom<R->CoordinateRing(PP)|[0,0,0,0,a,b,c]>;
S:=Scheme(PP,[h(g) : g in Basis(J)]);
comps:=IrreducibleComponents(S);
Degree(S) eq 7;
pts:=[
   // These are intersections with X1, defining C from Examples 3.3 and 5.10, that cover E with j(E)=0 and j(E)=1728, respectively.
   [6, 12, 10], [3, 6 + 6*w, 4 + 6*w],  [3, 6 + 6*w^2, 4 + 6*w^2],
   
   // These define the class of C: y^2 = x^6 + 3*x^4 - 6*x^2 - 8, that is a 3-cover of E with j(E)=287496 (CM by sqrt(-4))
   [3*(4 + 17*i), 4*(7 + 3*i), 24*(1 + i)],  [3*(4 - 17*i), 4*(7 - 3*i), 24*(1 - i)],
   
    // These define the class of C: y^2 = 8*x^6 - 2040*x^5 - 2244*x^4 - 5840*x^3 - 4230*x^2 - 4014*x - 837, that is a 3-cover of E with j(E)=-884736 (CM by (1+sqrt(-19))/2)
   [-21 + 9*u, -6 + 2*u, 6],  [-21 - 9*u, -6 - 2*u, 6]   
 ];
&and[PP!p in S : p in pts];

///////////////////////////////////////////////////////
// 1) the isomorphism class of C, covering j(E)=287496
///////////////////////////////////////////////////////
R<X>:=PolynomialRing(QQ);
K<i,q>:=ext<QQ|X^2+1,X^2-2>;
R<x>:=PolynomialRing(K);
a:=3*(4 + 17*i);
b:= 4*(7 + 3*i);
c:=24*(1 + i);
C:=HyperellipticCurve((x^3 + a*x^2 + b*x + c)*(4*c*x^3 + b^2*x^2 + 2*b*c*x + c^2));
C1:=HyperellipticCurve(x^6 + 3*x^4 - 6*x^2 - 8); // or x^5 + x^3 + 81/196*x
AbsoluteInvariants(C1) eq AbsoluteInvariants(C);
#Factorization((x^3 + a*x^2 + b*x + c)*(4*c*x^3 + b^2*x^2 + 2*b*c*x + c^2)) eq 6; // we added sqrt(2) to K to make P(x)Q(x) split completely

// the complementary degree-3 maps
A2<x,y>:=AffineSpace(K,2);
C:=Curve(A2, -y^2 + (x - i)*(x^2 + 4*(3 + 13*i)*x - 24*(1 - i)) * ((1 - i)*x + 3)*(3*x^2 + 4*(4 - i)*x + 12)); //bad primes: (1 + i),(1 + 2*i),3,(4 + i) above 2,5,17
E1:=Curve(A2, -y^2 + x^3 + 1/85*(-111*i + 393)*x^2 + 1/7225*(-28686*i + 48223)*x - 3*i + 3);
E2:=Curve(A2, -85*y^2 + x^3 + 1/85*(111*i + 393)*x^2 + 1/7225*(28686*i + 48223)*x + 3*i + 3);
f1:=map<C->E1|[ 
	i*(1 + 2*i)^2*(4 + i)^2 * x^2/((x - i)*(x^2 + 4*(3 + 13*i)*x - 24*(1 - i))), 
	(x + 4)*(x^2 - 4*x - 12*(1 + i))*y/((x - i)*(x^2 + 4*(3 + 13*i)*x - 24*(1 - i)))^2
]>;
f2:=map<C->A2|[
   -1/5/17 * ((5 - 2*i)*x + 18)^2*(19*x + 3*(5 + 2*i))/(((1 - i)*x + 3)*(4*(4 - i)*x + 3*x^2 + 12)),
   1/5^2/17^2 * y*((5 - 14*i)*x + 6)*(77*x^2 + 72*x - 36*i)/(((1 - i)*x + 3)*(4*(4 - i)*x + 3*x^2 + 12))^2
]>;

// the isomorphism class of E
R<X>:=PolynomialRing(K);
h:=hom<Parent(x)->R|[X,0]>;
jInvariant(EllipticCurve(h(Basis(Ideal(E1))[1]))) eq 287496;

// involutions of C
CC:=HyperellipticCurve((X - i)*(X^2 + 4*(3 + 13*i)*X - 24*(1 - i)) * ((1 - i)*X + 3)*(3*X^2 + 4*(4 - i)*X + 12)); // =P(x)*Q(x)/32
G,r,_:=AutomorphismGroup(CC);
L:=[];
for g in G do if Order(g) eq 2 then Append(~L, r(g)); end if; end for;
L;

/* Modulo the hyperelliptic one, there are two extra involutions and neither of them gives a complementary degree-3 covering by 
pre-composing with a given degree-3 covering. */
inv1:=map<C->C|[ 3*((1 + 10*i)*x - 6*(1 - 2*i))/((1 - 6*i)*x - 3*(1 + 10*i)), 27*(478 + 621*i)*y/((1 - 6*i)*x - 3*(1 + 10*i))^3 ]>;
inv2:=map<C->C|[ -3*((1 + 4*i)*x - 12*(1 - i))/((17 + 6*i)*x + 3*(1 + 4*i)), 27*(621 - 478*i)*y/((17 + 6*i)*x + 3*(1 + 4*i))^3 ]>;


///////////////////////////////////////////////////////
// 2) the isomorphism class of C, covering j(E)=-884736
///////////////////////////////////////////////////////
R<X>:=PolynomialRing(QQ);
K<u>:=ext<QQ|X^2+19>;
R<x>:=PolynomialRing(K);
K<v>:=ext<K|x^3 + (9*u - 21)*x^2 + (2*u - 6)*x + 6>;
R<x>:=PolynomialRing(K);
a:=9*u - 21;
b:=2*u - 6;
c:=6;
C:=HyperellipticCurve((x^3 + a*x^2 + b*x + c)*(4*c*x^3 + b^2*x^2 + 2*b*c*x + c^2));
C2:=HyperellipticCurve(8*x^6 - 2040*x^5 - 2244*x^4 - 5840*x^3 - 4230*x^2 - 4014*x - 837);
AbsoluteInvariants(C2) eq AbsoluteInvariants(C);
#Factorization((x^3 + a*x^2 + b*x + c)*(4*c*x^3 + b^2*x^2 + 2*b*c*x + c^2)) eq 6;

A2<x,y>:=AffineSpace(K,2);
C:=Curve(A2, -y^2 + (x^3 + (9*u - 21)*x^2 + (2*u - 6)*x + 6) * (6*x^3 - 2*(5 + 3*u)*x^2 - 6*(3 - u)*x + 9)); //bad primes: 2, 3, u+8 (above 83)
E1:=Curve(A2, - y^2 + x^3 + 1/83*(90*u - 222)*x^2 + 1/6889*(-13448*u - 34512)*x + 6);
E2:=Curve(A2, -83*y^2 + x^3 + 1/83*(90*u + 222)*x^2 + 1/6889*(13448*u - 34512)*x  - 6
);
f1:=map<C->E1|[
   (u+8)^2 * x^2/(x^3 + (9*u - 21)*x^2 + (2*u - 6)*x + 6),
   y * (x^3 + 2*(3 - u)*x - 12)/(x^3 + (9*u - 21)*x^2 + (2*u - 6)*x + 6)^2
]>;
f2:=map<C->E2|[
   1/83 * (37*x - 3*(u + 3))*((u - 3)*x + 9)^2/(6*x^3 - 2*(5 + 3*u)*x^2 - 6*(3 - u)*x + 9), 
   1/6889 * y*(4*(74*u + 207)*x^3 - 12*(15*u - 29)*x^2 - 9*(u - 3)*x - 27)/(6*x^3 - 2*(5 + 3*u)*x^2 - 6*(3 - u)*x + 9)^2
]>;

// the isomorphism class of E
R<X>:=PolynomialRing(K);
h:=hom<Parent(x)->R|[X,0]>;
jInvariant(EllipticCurve(h(Basis(Ideal(E1))[1]))) eq -884736;

// involutions of C
CC:=HyperellipticCurve((X^3 + (9*u - 21)*X^2 + (2*u - 6)*X + 6) * (6*X^3 - 2*(5 + 3*u)*X^2 - 6*(3 - u)*X + 9)); // =6*P(x)*Q(x)
G,r,_:=AutomorphismGroup(CC);
L:=[];
for g in G do if Order(g) eq 2 then Append(~L, r(g)); end if; end for;
L;

// Modulo the hyperelliptic one, there is one extra involution and it does not give a complementary degree-3 covering by 
pre-composing with a given degree-3 covering.
inv:=map<C->C|[-6*(50*x - 21 - 6*u)/((19*u - 21)*x + 300), y*216*(93548 + 3103*u)/((19*u - 21)*x + 300)^3]>;


/*  A somewhat relevant remark;
    If we search for all curves defined by Y1 that have additional involutions, we will also find curves defined by:
    1) [(801 + 513*u)/8, -(27+19*u)/2, 30], where  u^2 = -7
    2) [(1/152909827803677200)*(36035280094210030858 - 29586707794230106601379*u + 8695840690351755182659359*u^2 - 
    944599229397032231472484257*u^3 + 14789245937239768014634305578*u^4 - 90309903009272480067639633717*u^5), u, -3*u^2], where
     653294184733*u^6 - 109474575246*u^5 + 7241041409*u^4 - 88962570*u^3 + 454394*u^2 - 1080*u + 1 = 0
*/
