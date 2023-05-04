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


a:=-(t^12 + 16*t^11 + 128*t^10 + 672*t^9 + 2560*t^8 + 7408*t^7 + 16608*t^6 + 28912*t^5 + 38528*t^4 + 37920*t^3 + 25600*t^2 + 10000*t + 1250);
b:=2*t^12 + 80*t^11 + 1024*t^10 + 7584*t^9 + 38528*t^8 + 144560*t^7 + 415200*t^6 + 926000*t^5 + 1600000*t^4 + 2100000*t^3 + 2000000*t^2 + 1250000*t + 390625;
c:=-t^12;
C:=Curve(P2, -Y^2*Z^4 + X^6 + a*X^4*Z^2 + b*X^2*Z^4 + c*Z^6);
E1:=f1(C);
E2:=f2(C);
E1:=EllipticCurve(E1,E1![0,1,0]);
E2:=EllipticCurve(E2,E2![0,1,0]);
j1:=jInvariant(E1);
j2:=jInvariant(E2);
// Phi(25,j1,j2) eq 0;  // not implemented in Magma
<j1,j2> eq <(t^10 + 10*t^9 + 55*t^8 + 200*t^7 + 525*t^6 + 1010*t^5 + 1425*t^4 + 1400*t^3 + 875*t^2 + 250*t + 5)^3/(t*(t^4 + 5*t^3 + 15*t^2 + 25*t + 25)), 
            (t^10 + 250*t^9 + 4375*t^8 + 35000*t^7 + 178125*t^6 + 631250*t^5 + 1640625*t^4 + 3125000*t^3 + 4296875*t^2 + 3906250*t + 1953125)^3/(t^25*(t^4 + 5*t^3 + 15*t^2 + 25*t + 25))>;

// this takes a while over QQ; it is better tested in characteristic p
D:=DivisionPolynomial(E1,25);
F:=[f[1] : f in Factorization(D)];
E:=IsogenyFromKernel(E1,F[1]*F[2]);
IsIsomorphic(E,E2);

C:=HyperellipticCurve(x^6 + a*x^4 + b*x^2 + c);
C;
