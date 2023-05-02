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
a:=
b:=
c:=
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
Phi(5,j1,j2) eq 0;

D:=DivisionPolynomial(E1,5);
F:=[f[1] : f in Factorization(D)];
E:=IsogenyFromKernel(E1,F[1]^2);
IsIsomorphic(E,E2) eq true;

C1:=HyperellipticCurve((x^3 + a*x^2 + b*x + c)*(4*c*x^3 + b^2*x^2 + 2*b*c*x + c^2));
C2:=HyperellipticCurve();
IsQuadraticTwist(C1,C2);




/****** CASE 2 ******/
// verification is very slow even over a finite field.
F:=GF(11);
R<x>:=PolynomialRing(F);
F<w>:=ext<QQ|x^2+x+1>;
K<t>:=FunctionField(F);
R<S>:=PolynomialRing(K);
K<s>:=ext<K|S^2 + t*S + S - (t^3 + t^2 - 5*t + 2)>;
R<x>:=PolynomialRing(K);
P2<X,Y,Z>:=ProjectiveSpace(K,2);

u:=(s+t+2)/t;
a:=u^10 + 4*u^9 + 5*u^8 - 17*u^7 - 69*u^6 - 80*u^5 + 63*u^4 + 268*u^3 + 235*u^2 + 25*u + 125;
b:=48*u^10 - 48*u^9 - 912*u^8 - 3504*u^7 - 4272*u^6 + 6240*u^5 + 31200*u^4 + 48000*u^3 + 30000*u^2;
c:=64*u^15 + 768*u^14 + 4032*u^13 + 10432*u^12 + 3840*u^11 - 65472*u^10 - 232960*u^9 - 327360*u^8 + 96000*u^7 + 1304000*u^6 + 2520000*u^5 + 2400000*u^4 + 1000000*u^3;

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

p:=(t^6*(390625 + (1875000*(2 + s + t))/t + (3937500*(2 + s + t)^2)/t^2 + 
     (4481250*(2 + s + t)^3)/t^3 + (2411250*(2 + s + t)^4)/t^4 - (475500*(2 + s + t)^5)/t^5 - 
     (1726425*(2 + s + t)^6)/t^6 - (1127460*(2 + s + t)^7)/t^7 - (146571*(2 + s + t)^8)/t^8 + 
     (247360*(2 + s + t)^9)/t^9 + (171840*(2 + s + t)^10)/t^10 + (33330*(2 + s + t)^11)/t^11 - 
     (15165*(2 + s + t)^12)/t^12 - (11220*(2 + s + t)^13)/t^13 - (2415*(2 + s + t)^14)/t^14 + 
     (270*(2 + s + t)^15)/t^15 + (270*(2 + s + t)^16)/t^16 + (60*(2 + s + t)^17)/t^17 + 
     (5*(2 + s + t)^18)/t^18))/(327680*(2 + s + t)^6*(5 + (2*(2 + s + t))/t + (2 + s + t)^2/t^2)^7*
    (25 - (10*(2 + s + t))/t - (2 + s + t)^2/t^2 - (2*(2 + s + t)^3)/t^3 + (2 + s + t)^4/t^4)^9*
    (-5 - (2 + s + t)/t + (5*(2 + s + t)^2)/t^2 + (4*(2 + s + t)^3)/t^3 + (2 + s + t)^4/t^4)^18) + 
  (t^3*(-25 - (60*(2 + s + t))/t - (54*(2 + s + t)^2)/t^2 - (16*(2 + s + t)^3)/t^3 + 
     (9*(2 + s + t)^4)/t^4 + (6*(2 + s + t)^5)/t^5 + (2 + s + t)^6/t^6)*x)/
   (128*(2 + s + t)^3*(5 + (2*(2 + s + t))/t + (2 + s + t)^2/t^2)^3*
    (25 - (10*(2 + s + t))/t - (2 + s + t)^2/t^2 - (2*(2 + s + t)^3)/t^3 + (2 + s + t)^4/t^4)^4*
    (-5 - (2 + s + t)/t + (5*(2 + s + t)^2)/t^2 + (4*(2 + s + t)^3)/t^3 + (2 + s + t)^4/t^4)^9) + x^2;
E:=IsogenyFromKernel(E1,p);
IsIsomorphic(E,E2);
