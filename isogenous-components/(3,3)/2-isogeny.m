QQ:=Rationals();
R<x>:=PolynomialRing(QQ);
K<w>:=ext<QQ|x^2+x+1>;
K<t>:=FunctionField(K);
A2:=AffineSpace(K,2);
A1:=AffineSpace(K,1);
Phi:=func<n,j1,j2|map<A2->A1|[CoordinateRing(A2)!ClassicalModularPolynomial(n)]>([j1,j2])[1]>;
R<T>:=PolynomialRing(QQ);
h:=hom<K->R|T>;
R<x>:=PolynomialRing(K);
P2<X,Y,Z>:=ProjectiveSpace(K,2);

/****** CASE 1 ******/
u:=-2*(t^2-1)/(2*t - 1);
a:=-(u - 2)*(2*u^4 + 5*u^3 + 6*u^2 + 2*u + 8);
b:=6*(u - 2)*u^2*(2*u^3 - 3*u^2 - 12*u - 16);
c:=4*(u - 2)^2*u^3*(u + 1)*(u + 4)*(2*u^2 + u + 8);
d1:=a^2*b^2 - 4*b^3 - 4*a^3*c + 18*a*b*c - 27*c^2;
d2:=b^3 - 27*c^2;

E1:=Curve(P2, d1*X^3 - 2*a*b^2*X^2*Z + 12*a^2*c*X^2*Z - 18*b*c*X^2*Z - Y^2*Z + b^2*X*Z^2 - 12*a*c*X*Z^2 + 4*c*Z^3);
E2:=Curve(P2, -X^3 - a*b^3*X^2*Z + 27*b^2*c*X^2*Z - 54*a*c^2*X^2*Z + d2*Y^2*Z - b^7*X*Z^2 + 18*a*b^5*c*X*Z^2 - 54*a^2*b^3*c^2*X*Z^2 - 189*b^4*c^2*X*Z^2
              + 972*a*b^2*c^3*X*Z^2 - 729*a^2*c^4*X*Z^2 -729*b*c^4*X*Z^2 + 8*b^9*c*Z^3 - 108*a*b^7*c^2*Z^3 + 486*a^2*b^5*c^3*Z^3 + 324*b^6*c^3*Z^3
              -  729*a^3*b^3*c^4*Z^3 - 2916*a*b^4*c^4*Z^3 + 6561*a^2*b^2*c^5*Z^3 + 4374*b^3*c^5*Z^3 - 19683*a*b*c^6*Z^3 + 19683*c^7*Z^3);
E1:=EllipticCurve(E1,E1![0,1,0]);
E2:=EllipticCurve(E2,E2![0,1,0]);

j1:=jInvariant(E1);
j2:=jInvariant(E2);
Phi(2,j1,j2) eq 0;
<j1,j2> eq <64*(t^3 - 3*t^2 + 9*t - 5)^3*(t^3 + 3*t^2 - 3*t + 1)^3/((t - 1)^6*(t + 1)^6*(2*t - 1)^3), 
	    64*(2*t^3 - 1)^3*(2*t^3 - 6*t + 5)^3/((t - 1)^3*(t + 1)^3*(2*t - 1)^6)>;

D:=DivisionPolynomial(E1,2);
F:=[f[1] : f in Factorization(D)];
E:=IsogenyFromKernel(E1,F[1]);
IsIsomorphic(E,E2) eq true;

C1:=HyperellipticCurve((x^3 + a*x^2 + b*x + c)*(4*c*x^3 + b^2*x^2 + 2*b*c*x + c^2));
C2:=HyperellipticCurve(x*((2*t - 1)^3*(t^2 - t + 1)^2*(t^2 + 2*t - 2)*x^2 + 2*(2*t - 1)*(t^2 - 1)*(t^2 - t + 1)^2*(t^2 + 2*t - 2)*(t^2 + 8*t - 5)*x + (t^2 - 1)^2*(4*t^4 - 2*t^3 + 9*t^2 - 14*t + 7)^2)
	*(4*(2*t - 1)^2*(t^2 - t + 1)^2*(t^2 + 2*t - 2)^3*x^2 + 12*(2*t - 1)*(t^2 - 1)*(t^2 - t + 1)^2*(t^2 + 2*t - 2)^2*(4*t^2 + 2*t - 5)*x + 9*(t^2 - 1)^3*(4*t^4 - 2*t^3 + 9*t^2 - 14*t + 7)^2)
);
IsQuadraticTwist(C1,C2);




/****** CASE 2 ******/
a:= t^5 + (3*w - 4)*t^4 - (12*w + 14)*t^3 - (24*w + 8)*t^2 - 40*t - 32;
b:= 48*w * t^2 * (t + 1) * (t^3 - (3*w + 6)*t^2 - 12*w*t + 16);
c:= -64 * t^3 * (t + 1)^2 * (t + 4) * (t - 2) * (t^2 + (9*w + 2)*t - 8);
d1:=a^2*b^2 - 4*b^3 - 4*a^3*c + 18*a*b*c - 27*c^2;
d2:=b^3 - 27*c^2;

E1:=Curve(P2, d1*X^3 - 2*a*b^2*X^2*Z + 12*a^2*c*X^2*Z - 18*b*c*X^2*Z - Y^2*Z + b^2*X*Z^2 - 12*a*c*X*Z^2 + 4*c*Z^3);
E2:=Curve(P2, -X^3 - a*b^3*X^2*Z + 27*b^2*c*X^2*Z - 54*a*c^2*X^2*Z + d2*Y^2*Z - b^7*X*Z^2 + 18*a*b^5*c*X*Z^2 - 54*a^2*b^3*c^2*X*Z^2 - 189*b^4*c^2*X*Z^2
              + 972*a*b^2*c^3*X*Z^2 - 729*a^2*c^4*X*Z^2 -729*b*c^4*X*Z^2 + 8*b^9*c*Z^3 - 108*a*b^7*c^2*Z^3 + 486*a^2*b^5*c^3*Z^3 + 324*b^6*c^3*Z^3
              - 729*a^3*b^3*c^4*Z^3 - 2916*a*b^4*c^4*Z^3 + 6561*a^2*b^2*c^5*Z^3 + 4374*b^3*c^5*Z^3 - 19683*a*b*c^6*Z^3 + 19683*c^7*Z^3);
E1:=EllipticCurve(E1,E1![0,1,0]);
E2:=EllipticCurve(E2,E2![0,1,0]);

j1:=jInvariant(E1);
j2:=jInvariant(E2);
Phi(2,j1,j2) eq 0;
<j1,j2> eq <(t + 4)^3*(t^3 - 12*t^2 + 48*t + 64)^3/((t - 8)^2*t^6*(t + 1)), (t - 2)^3*(t^3 - 6*t^2 - 12*t - 8)^3/((t - 8)*t^3*(t + 1)^2)>;

D:=DivisionPolynomial(E1,2);
F:=[f[1] : f in Factorization(D)];
E:=IsogenyFromKernel(E1,F[1]);
IsIsomorphic(E,E2) eq true;

P:=16*x^2 + t*(t^3 + (32*w + 4)*t^2 - (32*w + 88)*t + 64*w^2)*x + w*t^2* (t + 1)*(t^2 + (9*w + 2)*t - 8)^2;
Q:=16*(t - 8)*x^2 + 24*w*t*(t^3 + (7*w - 4)*t^2 - (28*w + 32)*t - 8*w)*x + 9*w^2*t^3*(t^2 + (9*w + 2)*t - 8)^2;
C1:=HyperellipticCurve((x^3 + a*x^2 + b*x + c)*(4*c*x^3 + b^2*x^2 + 2*b*c*x + c^2));
C2:=HyperellipticCurve(x * P * Q);
IsQuadraticTwist(C1,C2);
