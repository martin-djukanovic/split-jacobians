QQ:=Rationals();
K<t>:=FunctionField(QQ);
R<T>:=PolynomialRing(QQ);
h:=hom<K->R|T>;
R<x>:=PolynomialRing(K);

// the first family is genus-two curves with automorphism group D8 (dihedral group with 8 elements).
a:=t;
b:=t;
c:=1;
P2<X,Y,Z>:=ProjectiveSpace(K,2);
C1:=Curve(P2, -Y^2*Z^4 + X^6 + a*X^4*Z^2 + b*X^2*Z^4 + c*Z^6);
C2:=Curve(P2, -2*Y^2*Z^4 + (t + 1)*X^6 - (t - 15)*X^4*Z^2 - (t - 15)*X^2*Z^4 + (t + 1)*Z^6);
iso:=map<C1->C2|[ (X - Z)*(X + Z)^2, 4*Y*Z^2, (X + Z)^3 ]>;

f1:=map<P2->P2|[X^2, Y*Z, Z^2]>;
f2:=map<P2->P2|[X*Z^2, Y*Z^2, X^3]>;
E1:=f1(C1);
E1 eq f2(C1);
E1:=EllipticCurve(E1,E1![0,1,0]);
jInvariant(E1);

E2:=f1(C2);
E2 eq f2(C2);
E2:=EllipticCurve(E2,E2![0,1,0]);
jInvariant(E2);

// the curves E1 and E2 are 2-isogenous.
E:=IsogenyFromKernel(E1,x+1);
IsIsomorphic(E,E2);


// the second family
a:=(t + 3);
b:=t;
c:=-1;
C:=Curve(P2, -Y^2*Z^4 + X^6 + a*X^4*Z^2 + b*X^2*Z^4 + c*Z^6);
E1:=f1(C);
E2:=f2(C);
E1:=EllipticCurve(E1,E1![0,1,0]);
E2:=EllipticCurve(E2,E2![0,1,0]);
IsIsomorphic(E1,E2);
jInvariant(E1);
