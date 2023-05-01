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


a:=-(t^6 + 16*t^5 + 112*t^4 + 432*t^3 + 944*t^2 + 1040*t + 338);
b:=2*t^6 + 80*t^5 + 944*t^4 + 5616*t^3 + 18928*t^2 + 35152*t + 28561;
c:=-t^6;
C:=Curve(P2, -Y^2*Z^4 + X^6 + a*X^4*Z^2 + b*X^2*Z^4 + c*Z^6);
E1:=f1(C);
E2:=f2(C);
E1:=EllipticCurve(E1,E1![0,1,0]);
E2:=EllipticCurve(E2,E2![0,1,0]);
j1:=jInvariant(E1);
j2:=jInvariant(E2);
Phi(13,j1,j2) eq 0;

D:=DivisionPolynomial(E1,13);
D:=Factorization(D)[1][1];
E:=IsogenyFromKernel(E1,D^2);
IsIsomorphic(E,E2);

C:=HyperellipticCurve(x^6 + a*x^4 + b*x^2 + c);
C;
