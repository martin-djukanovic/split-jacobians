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
a := -(t + 18);
b := 2*t + 81;
c := -t;
C:=Curve(P2, -Y^2*Z^4 + X^6 + a*X^4*Z^2 + b*X^2*Z^4 + c*Z^6);
E1:=f1(C);
E2:=f2(C);
E1:=EllipticCurve(E1,E1![0,1,0]);
E2:=EllipticCurve(E2,E2![0,1,0]);
j1:=jInvariant(E1);
j2:=jInvariant(E2);
Phi(3,j1,j2) eq 0;
<j1,j2> eq <(t + 3)^3*(t + 27)/t, (t + 27)*(t + 243)^3/t^3>;

D:=DivisionPolynomial(E1,3);
D:=Factorization(D)[1][1];
E:=IsogenyFromKernel(E1,D);
IsIsomorphic(E,E2);

C:=HyperellipticCurve(s^3*x^6 + s^2*a*x^4 + s*b*x^2 + c);
C;

/****** CASE 2 ******/
a:=t^4 + 8*t^3 + 42*t^2 + 144*t - 243;
b:=16*t^5 - 256*t^4 - 2016*t^3 - 10368*t^2 - 34992*t;
c:=-4096*t^5;
s:=t;
C:=Curve(P2, -Y^2*Z^4 + s^3*X^6 + s^2*a*X^4*Z^2 + s*b*X^2*Z^4 + c*Z^6);
E1:=f1(C);
E2:=f2(C);
E1:=EllipticCurve(E1,E1![0,1,0]);
E2:=EllipticCurve(E2,E2![0,1,0]);
j1:=jInvariant(E1);
j2:=jInvariant(E2);
Phi(3,j1,j2) eq 0;
<j1,j2> eq <(t^2 + 3)^3*(t^2 + 27)/t^2, (t^2 + 27)*(t^2 + 243)^3/t^6>;

D:=DivisionPolynomial(E1,3);
D:=Factorization(D)[1][1];
E:=IsogenyFromKernel(E1,D);
IsIsomorphic(E,E2);

C1:=HyperellipticCurve(s^3*x^6 + s^2*a*x^4 + s*b*x^2 + c);
C2:=HyperellipticCurve(t*x^6 + (t^4 + 8*t^3 + 42*t^2 + 144*t - 243)*x^4 + 16*(t^4 - 16*t^3 - 126*t^2 - 648*t - 2187)*x^2 - 4096*t^3);
IsIsomorphic(C1,C2);


/****** CASE 3 ******/
a:=(t + 3)*(t^4 + 2*t^3 - 12*t^2 + 78*t + 27);
b:=16*t*(t + 1)*(t + 3)*(t^4 + 26*t^3 - 36*t^2 + 54*t + 243);
c:=4096*t^5*(t + 1)^2*(t + 9);
s:=t*(t+1);
C:=Curve(P2, -Y^2*Z^4 + s^3*X^6 + s^2*a*X^4*Z^2 + s*b*X^2*Z^4 + c*Z^6);
E1:=f1(C);
E2:=f2(C);
E1:=EllipticCurve(E1,E1![0,1,0]);
E2:=EllipticCurve(E2,E2![0,1,0]);
j1:=jInvariant(E1);
j2:=jInvariant(E2);
Phi(3,j1,j2) eq 0;
<j1,j2> eq <(t + 3)^3*(t^3 + 9*t^2 + 3*t + 3)^3/(t^2*(t + 1)^3*(t + 9)), (t + 3)^3*(t^3 + 9*t^2 + 243*t + 243)^3/(t^6*(t + 1)*(t + 9)^3)>;

D:=DivisionPolynomial(E1,3);
D:=Factorization(D)[1][1];
E:=IsogenyFromKernel(E1,D);
IsIsomorphic(E,E2);

C1:=HyperellipticCurve(s^3*x^6 + s^2*a*x^4 + s*b*x^2 + c);
C2:=HyperellipticCurve(((t + 1)*x^2 + 16*(t + 9))*(t*x^4 + (t^4 + 4*t^3 - 10*t^2 + 36*t + 81)*x^2 + 256*t^3));
IsQuadraticTwist(C1,C2);
