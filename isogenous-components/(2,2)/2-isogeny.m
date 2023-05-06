QQ:=Rationals();
K<t>:=FunctionField(QQ);
A2:=AffineSpace(K,2);
A1:=AffineSpace(K,1);
Phi:=func<n,j1,j2|map<A2->A1|[CoordinateRing(A2)!ClassicalModularPolynomial(n)]>([j1,j2])[1]>;
R<x>:=PolynomialRing(K);
P2<X,Y,Z>:=ProjectiveSpace(K,2);
f1:=map<P2->P2|[X^2, Y*Z, Z^2]>;
f2:=map<P2->P2|[X*Z^2, Y*Z^2, X^3]>;

/****** CASE 1 ******/
a:=-2*t^3 - 2*t^2 - 2*t + 1;
b:=t*(t^3 - 2*t^2 - 2*t - 2);
c:=t^4;
s:=-2*t;
C:=Curve(P2, -Y^2*Z^4 + s^3*X^6 + s^2*a*X^4*Z^2 + s*b*X^2*Z^4 + c*Z^6);
E1:=f1(C);
E2:=f2(C);
E1:=EllipticCurve(E1,E1![0,1,0]);
E2:=EllipticCurve(E2,E2![0,1,0]);
j1:=jInvariant(E1);
j2:=jInvariant(E2);
Phi(2,j1,j2) eq 0;
<j1,j2> eq <64*(1 + 4*t^2)^3/t^2, 64*(4 + t^2)^3/t^4>;

D:=DivisionPolynomial(E1,2);
D:=Factorization(D)[1][1];
E:=IsogenyFromKernel(E1,D);
IsIsomorphic(E,E2);

C1:=HyperellipticCurve(s^3*x^6 + s^2*a*x^4 + s*b*x^2 + c);
C2:=HyperellipticCurve((2*t*x^2 - 1)*(4*x^4 + 4*(t^2 + t + 1)*x^2 + t^2));
IsQuadraticTwist(C1,C2);


/****** CASE 2 ******/
a:=2 - 7*t + t^2 + t^3 - t^4;
b:=-(-1 + t)*t*(-8 + 4*t + 2*t^2 - 7*t^3 + t^4);
c:=4*(-2 + t)*(-1 + t)^2*t^4;
s:=t*(t-1);
C:=Curve(P2, -Y^2*Z^4 + s^3*X^6 + s^2*a*X^4*Z^2 + s*b*X^2*Z^4 + c*Z^6);
E1:=f1(C);
E2:=f2(C);
E1:=EllipticCurve(E1,E1![0,1,0]);
E2:=EllipticCurve(E2,E2![0,1,0]);
j1:=jInvariant(E1);
j2:=jInvariant(E2);
Phi(2,j1,j2) eq 0;
<j1,j2> eq <256*(t^4 - 4*t^3 + 5*t^2 - 2*t + 1)^3/((t - 2)^2*(t - 1)^4*t^2), 16*(t^4 - 4*t^3 + 20*t^2 - 32*t + 16)^3/((t - 2)^4*(t - 1)^2*t^4)>;

D:=DivisionPolynomial(E1,2);
D:=Factorization(D)[2][1];
E:=IsogenyFromKernel(E1,D);
IsIsomorphic(E,E2);

C1:=HyperellipticCurve(s^3*x^6 + s^2*a*x^4 + s*b*x^2 + c);
C2:=HyperellipticCurve((x^2 - t^2)*(t*x^2 + t - 2)*((t - 1)*x^2 - 4)); // swap t by -t to simplify
IsQuadraticTwist(C1,C2);
