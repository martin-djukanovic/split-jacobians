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
a:=-(t^4 + 16*t^3 + 96*t^2 + 240*t + 162);
b:=2*t^4 + 80*t^3 + 864*t^2 + 3888*t + 6561;
c:=-t^4;
C:=Curve(P2, -Y^2*Z^4 + X^6 + a*X^4*Z^2 + b*X^2*Z^4 + c*Z^6);
E1:=f1(C);
E2:=f2(C);
E1:=EllipticCurve(E1,E1![0,1,0]);
E2:=EllipticCurve(E2,E2![0,1,0]);
j1:=jInvariant(E1);
j2:=jInvariant(E2);
Phi(9,j1,j2) eq 0;

D:=DivisionPolynomial(E1,9);
F:=[f[1] : f in Factorization(D)];
E:=IsogenyFromKernel(E1,F[1]*F[2]);
IsIsomorphic(E,E2);

C:=HyperellipticCurve(x^6 + a*x^4 + b*x^2 + c);
C;



/****** CASE 2 ******/
a:=t^16 - 8*t^15 + 24*t^14 - 24*t^13 - 32*t^12 + 96*t^11 - 64*t^10 + 64*t^9 - 288*t^8
   + 368*t^7 + 320*t^6 + 768*t^5 + 528*t^4 + 128*t^3 - 384*t^2 - 512*t - 256;
b:=16*(t - 1)*t^4*(t^2 + t + 1)*(t^16 + 16*t^15 - 144*t^14 + 456*t^13 - 800*t^12 + 1152*t^11 - 
    1792*t^10 + 1792*t^9 - 16*t^7 - 3328*t^6 + 2304*t^5 + 14352*t^4 + 21248*t^3 + 16128*t^2 + 
    7168*t + 512);
c:=4096*(t - 1)^11*t^8*(t + 2)^4*(t^2 + t + 1)^3;
s:=t^3 - 1;

C:=Curve(P2, -Y^2*Z^4 + s^3*X^6 + s^2*a*X^4*Z^2 + s*b*X^2*Z^4 + c*Z^6);
E1:=f1(C);
E2:=f2(C);
E1:=EllipticCurve(E1,E1![0,1,0]);
E2:=EllipticCurve(E2,E2![0,1,0]);
j1:=jInvariant(E1);
j2:=jInvariant(E2);
Phi(9,j1,j2) eq 0;

D:=DivisionPolynomial(E1,9);
F:=[f[1] : f in Factorization(D)];
E:=IsogenyFromKernel(E1,F[1]*F[2]);
IsIsomorphic(E,E2);

C1:=HyperellipticCurve(s^3*x^6 + s^2*a*x^4 + s*b*x^2 + c);
C2:=HyperellipticCurve((x^2 + 16*(t + 2)^4) * ((t^3 - 1)*x^4 + t^4*(t^12 - 8*t^11 + 24*t^10 - 24*t^9 - 32*t^8 + 96*t^7 - 64*t^6 + 64*t^5 - 288*t^4 + 352*t^3 + 192*t^2 + 384*t + 32)*x^2 + 256*(t^2 - t)^8*(t^3 - 1)));
IsIsomorphic(C1,C2) eq true;
