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
a:=-(t^3 + 16*t^2 + 80*t + 98);
b:=2*t^3 + 80*t^2 + 784*t + 2401;
c:=-t^3;
C:=Curve(P2, -Y^2*Z^4 + X^6 + a*X^4*Z^2 + b*X^2*Z^4 + c*Z^6);
E1:=f1(C);
E2:=f2(C);
E1:=EllipticCurve(E1,E1![0,1,0]);
E2:=EllipticCurve(E2,E2![0,1,0]);
j1:=jInvariant(E1);
j2:=jInvariant(E2);
Phi(7,j1,j2) eq 0;
<j1,j2> eq <(t^2 + 5*t + 1)^3*(t^2 + 13*t + 49)/t, (t^2 + 13*t + 49)*(t^2 + 245*t + 2401)^3/t^7>;

D:=DivisionPolynomial(E1,7);
D:=Factorization(D)[1][1];
E:=IsogenyFromKernel(E1,D);
IsIsomorphic(E,E2);

C:=HyperellipticCurve(x^6 + a*x^4 + b*x^2 + c);
C;



/****** CASE 2 ******/
a:=t^8 + 8*t^7 + 38*t^6 + 128*t^5 + 327*t^4 + 640*t^3 + 910*t^2 + 784*t - 343;
b:=16*t^9 - 256*t^8 - 2080*t^7 - 10240*t^6 - 36624*t^5 - 100352*t^4 - 208544*t^3 - 307328*t^2 - 268912*t;
c:=-4096*t^9;
s:=t;

C:=Curve(P2, -Y^2*Z^4 + s^3*X^6 + s^2*a*X^4*Z^2 + s*b*X^2*Z^4 + c*Z^6);
E1:=f1(C);
E2:=f2(C);
E1:=EllipticCurve(E1,E1![0,1,0]);
E2:=EllipticCurve(E2,E2![0,1,0]);
j1:=jInvariant(E1);
j2:=jInvariant(E2);
Phi(7,j1,j2) eq 0;
<j1,j2> eq <(t^2 - t + 7)*(t^2 + t + 7)*(t^4 + 5*t^2 + 1)^3/t^2, (t^2 - t + 7)*(t^2 + t + 7)*(t^4 + 245*t^2 + 2401)^3/t^14>;

D:=DivisionPolynomial(E1,7);
D:=Factorization(D)[1][1];
E:=IsogenyFromKernel(E1,D);
IsIsomorphic(E,E2);

C1:=HyperellipticCurve(s^3*x^6 + s^2*a*x^4 + s*b*x^2 + c);
C2:=HyperellipticCurve(t*x^6 + (t^8 + 8*t^7 + 38*t^6 + 128*t^5 + 327*t^4 + 640*t^3 + 910*t^2 + 784*t - 343)*x^4 + 
  (16*t^8 - 256*t^7 - 2080*t^6 - 10240*t^5 - 36624*t^4 - 100352*t^3 - 208544*t^2 - 307328*t - 268912)*x^2 - 4096*t^7);
IsIsomorphic(C1,C2) eq true;
