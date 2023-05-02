QQ:=Rationals();
K<t>:=FunctionField(K);
A2:=AffineSpace(K,2);
A1:=AffineSpace(K,1);
Phi:=func<n,j1,j2|map<A2->A1|[CoordinateRing(A2)!ClassicalModularPolynomial(n)]>([j1,j2])[1]>;
R<T>:=PolynomialRing(QQ);
h:=hom<K->R|T>;
R<x>:=PolynomialRing(K);
P2<X,Y,Z>:=ProjectiveSpace(K,2);

/****** CASE 1 ******/
C:=Curve(P2, - Y^2*Z^4 + X^6 + (-t^2 + 4*t + 10)*X^4*Z^2 + (2*t^2 + 40*t + 25)*X^2*Z^4 + (- t^2 + 20*t - 100)*Z^6);
E1:=Curve(P2, -2*Y^2*Z + (t - 10)*(t^2 + 2*t + 5)*X^3 + 8*(3*t - 25)*(t^2 + 2*t + 5)*X^2*Z + 64*(3*t^3 - 14*t^2 - 17*t - 80)*X*Z^2 + 512*(t - 1)^3*Z^3);
E2:=Curve(P2, -Y^2*Z + 8*(t^2 + 2*t + 5)*X^3 - 4*(t - 10)*(t + 65)*(t^2 + 2*t + 5)*X^2*Z + 2*(t - 10)^2*(54*t^3 + 1395*t^2 + 3400*t + 6875)*X*Z^2 - (t - 10)^3*(9*t + 35)^3*Z^3);

// degree-3 coverings
f1:=map<C->E1|[
	-8*(X + Z)^2*(X + t*Z)*(X^3 + t*X^2*Z + (2*t + 5)*X*Z^2 + (t - 10)*Z^3),
	32*Y*Z^2*(X^3 - 5*X^2*Z +(15 - 4*t)*X*Z^2 + (12*t +  5)*Z^3),
	(X^3 + t*X^2*Z + (2*t + 5)*X*Z^2 + (t - 10)*Z^3)^2
]>;
f2:=map<C->E2|[
	(t - 10)*(X - 5*Z)^2*(2*t*X - t*Z + 5*X + 10*Z)*(-(t*X^2*Z) + 2*t*X*Z^2 - t*Z^3 + X^3 + 
    5*X*Z^2 + 10*Z^3), 4*(t - 10)^3*Y*Z^2*(t*X^2*Z + t*X^3 - t*X*Z^2 - t*Z^3 + 10*X^2*Z + 
    2*X^3 + 10*X*Z^2 + 10*Z^3), 2*(-(t*X^2*Z) + 2*t*X*Z^2 - t*Z^3 + X^3 + 5*X*Z^2 + 10*Z^3)^2
]>;

// degree-2 coverings
g1:=map<C->E1|[
	-8*X*(t^2*X^2 + 3*t*X^2 + t*Z^2 + 5*X^2 - 10*Z^2),
	16*(t - 10)*Y*Z^2,
	(t^2 + 2*t + 5)*X^3
]>;
g2:=map<C->E2|[
	(t - 10)*(27*t^2*Z^2 + t*X^2 + 35*t*Z^2 - 10*X^2 + 75*Z^2),
	2*(t - 10)^3*Y*Z, 
	2*(t^2 + 2*t + 5)*Z^2
]>;

E1:=EllipticCurve(E1,E1![0,1,0]);
E2:=EllipticCurve(E2,E2![0,1,0]);
j1:=jInvariant(E1);
j2:=jInvariant(E2);
Phi(5,j1,j2) eq 0;

D:=DivisionPolynomial(E1,5);
F:=[f[1] : f in Factorization(D)];
E:=IsogenyFromKernel(E1,F[1]^2);
IsIsomorphic(E,E2) eq true;




/****** CASE 2 ******/
// verification is very slow over Q
F:=GF(11);
R<x>:=PolynomialRing(F);
F<w>:=ext<QQ|x^2+x+1>;
K<u>:=FunctionField(F);
R<V>:=PolynomialRing(K);
K<v>:=ext<K|V^2 + u*V + V - (u^3 + u^2 - 5*u + 2)>;
A2:=AffineSpace(K,2);
A1:=AffineSpace(K,1);
Phi:=func<n,j1,j2|map<A2->A1|[CoordinateRing(A2)!ClassicalModularPolynomial(n)]>([j1,j2])[1]>;
R<x>:=PolynomialRing(K);
P2<X,Y,Z>:=ProjectiveSpace(K,2);

t:=(u+v+2)/u;
a:=t^10 + 4*t^9 + 5*t^8 - 17*t^7 - 69*t^6 - 80*t^5 + 63*t^4 + 268*t^3 + 235*t^2 + 25*t + 125;
b:=48*t^10 - 48*t^9 - 912*t^8 - 3504*t^7 - 4272*t^6 + 6240*t^5 + 31200*t^4 + 48000*t^3 + 30000*t^2;
c:=64*t^15 + 768*t^14 + 4032*t^13 + 10432*t^12 + 3840*t^11 - 65472*t^10 - 232960*t^9 - 327360*t^8 + 96000*t^7 + 1304000*t^6 + 2520000*t^5 + 2400000*t^4 + 1000000*t^3;
d1:=a^2*b^2 - 4*b^3 - 4*a^3*c + 18*a*b*c - 27*c^2;
d2:=b^3 - 27*c^2;

E1:=Curve(P2, d1*X^3 - 2*a*b^2*X^2*Z + 12*a^2*c*X^2*Z - 18*b*c*X^2*Z - Y^2*Z + b^2*X*Z^2 - 12*a*c*X*Z^2 + 4*c*Z^3);
E2:=Curve(P2, -X^3 - a*b^3*X^2*Z + 27*b^2*c*X^2*Z - 54*a*c^2*X^2*Z + d2*Y^2*Z - b^7*X*Z^2 + 18*a*b^5*c*X*Z^2 - 
  54*a^2*b^3*c^2*X*Z^2 - 189*b^4*c^2*X*Z^2 + 972*a*b^2*c^3*X*Z^2 - 729*a^2*c^4*X*Z^2 - 
  729*b*c^4*X*Z^2 + 8*b^9*c*Z^3 - 108*a*b^7*c^2*Z^3 + 486*a^2*b^5*c^3*Z^3 + 324*b^6*c^3*Z^3 - 
  729*a^3*b^3*c^4*Z^3 - 2916*a*b^4*c^4*Z^3 + 6561*a^2*b^2*c^5*Z^3 + 4374*b^3*c^5*Z^3 - 
  19683*a*b*c^6*Z^3 + 19683*c^7*Z^3);

E1:=EllipticCurve(E1,E1![0,1,0]);
E2:=EllipticCurve(E2,E2![0,1,0]);
j1:=jInvariant(E1);
j2:=jInvariant(E2);
Phi(5,j1,j2) eq 0;

p:=x^2 + (t^6 + 6*t^5 + 9*t^4 - 16*t^3 - 54*t^2 - 60*t - 25)/(128*t^3*(t^2 + 2*t + 5)^3*(t^4 - 2*t^3 - t^2 - 10*t + 25)^4*(t^4 + 4*t^3 + 5*t^2 - t - 5)^9)*x
+ (5*t^18 + 60*t^17 + 270*t^16 + 270*t^15 - 2415*t^14 - 11220*t^13 - 15165*t^12 + 33330*t^11 + 171840*t^10 + 247360*t^9
- 146571*t^8 - 1127460*t^7 - 1726425*t^6 - 475500*t^5 + 2411250*t^4 + 4481250*t^3 + 3937500*t^2 + 1875000*t + 390625)
/(327680*t^6*(t^2 + 2*t + 5)^7*(t^4 - 2*t^3 - t^2 - 10*t + 25)^9*(t^4 + 4*t^3 + 5*t^2 - t - 5)^18);
E:=IsogenyFromKernel(E1,p);
IsIsomorphic(E,E2);
