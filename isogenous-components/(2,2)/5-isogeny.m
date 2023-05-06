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
a:=-(t^2 + 16*t + 50);
b:=2*t^2 + 80*t + 625;
c:=-t^2;
C:=Curve(P2, -Y^2*Z^4 + X^6 + a*X^4*Z^2 + b*X^2*Z^4 + c*Z^6);
E1:=f1(C);
E2:=f2(C);
E1:=EllipticCurve(E1,E1![0,1,0]);
E2:=EllipticCurve(E2,E2![0,1,0]);
j1:=jInvariant(E1);
j2:=jInvariant(E2);
Phi(5,j1,j2) eq 0;
<j1,j2> eq <(t^2 + 10*t + 5)^3/t, (t^2 + 250*t + 3125)^3/t^5>;

D:=DivisionPolynomial(E1,5);
D:=Factorization(D)[1][1];
E:=IsogenyFromKernel(E1,D);
IsIsomorphic(E,E2);
C;



/****** CASE 2 ******/
a:=-(t^8 - 4*t^7 - 4*t^5 - 6*t^4 - 28*t^3 + 360*t^2 - 700*t + 125);
b:=-16*(t - 1)^2*t*(t^8 - 28*t^7 + 72*t^6 - 28*t^5 - 30*t^4 - 100*t^3 - 2500*t + 3125);
c:=4096*(t - 5)^2*(t - 1)^4*t^7;
s:=t;
C:=Curve(P2, -Y^2*Z^4 + s^3*X^6 + s^2*a*X^4*Z^2 + s*b*X^2*Z^4 + c*Z^6);
E1:=f1(C);
E2:=f2(C);
E1:=EllipticCurve(E1,E1![0,1,0]);
E2:=EllipticCurve(E2,E2![0,1,0]);
j1:=jInvariant(E1);
j2:=jInvariant(E2);
Phi(5,j1,j2) eq 0;
<j1,j2> eq <(t^6 - 10*t^5 + 35*t^4 - 60*t^3 + 55*t^2 - 10*t + 5)^3/((t - 5)*(t - 1)^5*t^2), 
            (t^6 - 10*t^5 + 275*t^4 - 1500*t^3 + 4375*t^2 - 6250*t + 3125)^3/((t - 5)^5*(t - 1)*t^10)>;

D:=DivisionPolynomial(E1,5);
D:=Factorization(D)[1][1];
E:=IsogenyFromKernel(E1,D);
IsIsomorphic(E,E2);

C1:=HyperellipticCurve(s^3*x^6 + s^2*a*x^4 + s*b*x^2 + c);
C2:=HyperellipticCurve((x^2 + 16*(t - 5)^2)*(t*x^4 - (t - 1)^2*(t^6 - 2*t^5 - 5*t^4 - 12*t^3 - 25*t^2 - 50*t + 125)*x^2 + 256*t^5*(t - 1)^4));
IsIsomorphic(C1,C2) eq true;
