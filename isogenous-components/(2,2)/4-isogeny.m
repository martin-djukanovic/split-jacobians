QQ:=Rationals();
K<t>:=FunctionField(QQ);
A2:=AffineSpace(K,2);
A1:=AffineSpace(K,1);
Phi:=func<n,j1,j2|map<A2->A1|[CoordinateRing(A2)!ClassicalModularPolynomial(n)]>([j1,j2])[1]>;
R<T>:=PolynomialRing(QQ);
h:=hom<K->R|T>;
R<x>:=PolynomialRing(K);
P2<X,Y,Z>:=ProjectiveSpace(K,2);
f1:=map<P2->P2|[X^2, Y*Z, Z^2]>;
f2:=map<P2->P2|[X*Z^2, Y*Z^2, X^3]>;



/****** CASE 1 ******/
a:=4*t^5 - 8*t^4 + 10*t^3 - 8*t^2 + 4*t + 1;
b:=t*(t^5 + 4*t^4 - 8*t^3 + 10*t^2 - 8*t + 4);
c:=t^6;
s:=t;
C:=Curve(P2, -Y^2*Z^4 + s^3*X^6 + s^2*a*X^4*Z^2 + s*b*X^2*Z^4 + c*Z^6);
E1:=f1(C);
E2:=f2(C);
E1:=EllipticCurve(E1,E1![0,1,0]);
E2:=EllipticCurve(E2,E2![0,1,0]);
j1:=jInvariant(E1);
j2:=jInvariant(E2);
Phi(4,j1,j2) eq 0;

D:=DivisionPolynomial(E1,4);
F:=[f[1] : f in Factorization(D)];
E:=IsogenyFromKernel(E1,F[1]^2*F[3]^2);
IsIsomorphic(E,E2);

C1:=HyperellipticCurve(s^3*x^6 + s^2*a*x^4 + s*b*x^2 + c);
C2:=HyperellipticCurve((t*x^2 + 1)*(x^4 + 2*(2*t^4 - 4*t^3 + 5*t^2 - 4*t + 2)*x^2 + t^4));
IsIsomorphic(C1,C2) eq true;



/****** CASE 2 ******/
a:=t^10 - 7*t^9 - 43*t^8 - 99*t^7 - 157*t^6 - 197*t^5 - 233*t^4 - 129*t^3 - 128*t^2 - 16*t - 16;
b:=-8*(t - 1)^3*(t + 1)^4*(t^2 + 1)*(t^10 + 5*t^9 + 11*t^8 + 15*t^7 + 14*t^6 + 22*t^5 + 10*t^4 + 18*t^3 + 16*t^2 + 8*t + 8);
c:=-64*(t - 1)^6*t^3*(t + 1)^9*(t^2 + 1)^3;
s:=-2*(-1 + t)*(1 + t^2);

C:=Curve(P2, -Y^2*Z^4 + s^3*X^6 + s^2*a*X^4*Z^2 + s*b*X^2*Z^4 + c*Z^6);
E1:=f1(C);
E2:=f2(C);
E1:=EllipticCurve(E1,E1![0,1,0]);
E2:=EllipticCurve(E2,E2![0,1,0]);
j1:=jInvariant(E1);
j2:=jInvariant(E2);
Phi(4,j1,j2) eq 0;

D2:=DivisionPolynomial(E1,2);
D4:=Quotrem(DivisionPolynomial(E1,4),D2);
F2:=Factorization(D2);
F4:=Factorization(D4);
p:=F2[3][1] * F4[2][1];
E,isog:=IsogenyFromKernel(E1,p^2);
IsIsomorphic(E,E2);

C1:=HyperellipticCurve(s^3*x^6 + s^2*a*x^4 + s*b*x^2 + c);
C2:=HyperellipticCurve(((t - 1)*x^2 + 4*(t + 1)*(t^2 + 1))*((t + 1)^4*x^2 - 4*(t - 1)^2)*(2*(t^2 + 1)*x^2 - (t - 1)^2*t^3));
IsQuadraticTwist(C1,C2);
