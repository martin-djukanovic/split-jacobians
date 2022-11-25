/* using a nice rational parametrization for q^2 = t^2 - 6*t - 3 we obtain a one-dimensional family of curves C over K,
   whose Jacobian is (3,3)-split as E x E, and (2,2)-split as E1 x E2.
*/
K<s>:=FunctionField(QQ);
t:=-(s^2 - s + 1)/(s + 1);
q:=(s^2 + 2*s - 2)/(s + 1);
q^2 eq t^2 - 6*t - 3;

// everything below is basically copied verbatim from complementary_twists.m; the difference is that the formulas for the j-invariants are in terms of s
A2<x,y>:=AffineSpace(K,2);
C:=Curve(A2, -y^2 + (4*t*x^3 + 3*(t + 1)*(t + 3)*x^2 + 12*t*(t + 1)*x + 4*t*(3*t + 1))*(4*(3*t + 1)*x^3 + 9*(t + 1)^2*x^2 + 6*(t + 1)*(3*t + 1)*x + (3*t + 1)^2));
E:=Curve(A2, -y^2 + x^3 + 3*(t + 1)*t*x^2 - 3*(t + 1)*(2*t^2 + 9*t + 3)*t^2*x/(t^2 - 6*t - 3) + (3*t + 1)*t^3);

f1:=map<C->E|[
  3*t*(t^2 - 6*t - 3) * x^2/(4*t*x^3 + 3*(t + 1)*(t + 3)*x^2 + 12*t*(t + 1)*x + 4*t*(3*t + 1)), 
  4*t^3 * y*(x^3 - 3*(t + 1)*x - 2*(3*t + 1))/(4*t*x^3 + 3*(t + 1)*(t + 3)*x^2 + 12*t*(t + 1)*x + 4*t*(3*t + 1))^2
]>;
f2:=map<C->E|[
  3*t/(t^2 - 6*t - 3) * ((t + 1)*x + (3*t + 1))^2*(4*(2*t + 1)*x + (t + 1)*(3*t + 1))/(4*(3*t + 1)*x^3 + 9*(t + 1)^2*x^2 + 6*(t + 1)*(3*t + 1)*x + (3*t + 1)^2), 
  q*4*t^3/(t^2 - 6*t - 3)^2 * y*((9*t^3 - 105*t^2 - 109*t - 27)*x^3 - 3*(7*t + 3)*(t + 1)*(3*t + 1)*x^2 - 3*t*(t + 1)*(3*t + 1)^2*x - t*(3*t + 1)^3)/(4*(3*t + 1)*x^3 + 9*(t + 1)^2*x^2 + 6*(t + 1)*(3*t + 1)*x + (3*t + 1)^2)^2
]>;

R<X>:=PolynomialRing(K);
h:=hom<CoordinateRing(A2)->R | [X,0]>;
j:=jInvariant(EllipticCurve(h(Basis(Ideal(E))[1])));
j eq -(27*s^3*(s^3 - 8)^3)/(s^3 + 1)^3;

C:=Curve(A2, -y^2 + (4*t*x^3 + 3*(t + 1)*(t + 3)*x^2 + 12*t*(t + 1)*x + 4*t*(3*t + 1))*(4*(3*t + 1)*x^3 + 9*(t + 1)^2*x^2 + 6*(t + 1)*(3*t + 1)*x + (3*t + 1)^2));
inv:=map<C->C|[
 -(3*t + 1)*((t + 1)*x + 3*t + 1)/(4*(2*t + 1)*x + (3*t + 1)*(t + 1)),
 -y*q*(3*t + 1)^3*(t^2 - 6*t - 3)/(4*(2*t + 1)*x + (3*t + 1)*(t + 1))^3
]>;

E1:=Curve(A2, -(-3*(t - 3)*(3*t + 1)*(t^2 - 6*t - 3) + 3*q*(3*t + 1)*(t^2 - 6*t + 3))*y^2
	+ x^3
	+ 3*(q*(9*t^3 - 33*t^2 - 3*t - 1) - (9*t^4 - 60*t^3 + 42*t^2 + 44*t + 3))*x^2
	- 12*(q*(3*t^3 + 13*t^2 - 33*t - 3) - t*(t + 6)*(3*t^2 - 14*t - 6))*x
	+ 12*(q*(t - 3)*(t^2 - 6*t + 3) - (t^4 - 12*t^3 + 42*t^2 - 36*t - 9))
);
E2:=Curve(A2, -(-3*(t - 3)*(3*t + 1)*(t^2 - 6*t - 3) - 3*q*(3*t + 1)*(t^2 - 6*t + 3))*y^2
	+ x^3
	+ 3*(-q*(9*t^3 - 33*t^2 - 3*t - 1) - (9*t^4 - 60*t^3 + 42*t^2 + 44*t + 3))*x^2
	- 12*(-q*(3*t^3 + 13*t^2 - 33*t - 3) - t*(t + 6)*(3*t^2 - 14*t - 6))*x
	+ 12*(-q*(t - 3)*(t^2 - 6*t + 3) - (t^4 - 12*t^3 + 42*t^2 - 36*t - 9))
);

g1:=map<C->E1|[6 * (3*t + 1 + (t + 1 - q)*x)^2/(3*t + 1 + (t + 1 + q)*x)^2, 8*(3*t+1) * y/(3*t + 1 + (t + 1 + q)*x)^3]>;
g2:=map<C->E2|[6 * (3*t + 1 + (t + 1 + q)*x)^2/(3*t + 1 + (t + 1 - q)*x)^2, 8*(3*t+1) * y/(3*t + 1 + (t + 1 - q)*x)^3]>;

u := -q-t;
p1 := (2*(u + 3)^2*(u^2 + 6*u - 3)*X + 5*u^5 - 15*u^4 + 18*u^3 - 54*u^2 + 9*u - 27)^2;
p2 := (2*(u^3 + 9*u^2 + 15*u - 9)*X + 2*u^5 - u^4 + 6*u^3 + 9)^2;

E:=EllipticCurve(h(Basis(Ideal(E))[1]));
yCoeff:=Coefficient(Basis(Ideal(E1))[1],y,2);
E1:=map<A2->A2|[-1/yCoeff*x, 1/yCoeff*y]>(E1);
E1:=EllipticCurve(h(Basis(Ideal(E1))[1]));
yCoeff:=Coefficient(Basis(Ideal(E2))[1],y,2);
E2:=map<A2->A2|[-1/yCoeff*x, 1/yCoeff*y]>(E2);
E2:=EllipticCurve(h(Basis(Ideal(E2))[1]));
IsIsomorphic(E1, IsogenyFromKernel(E,p1)) and IsIsomorphic(E2, IsogenyFromKernel(E,p2));

jInvariant(E1) eq -((27*s^3*(9*s^3 + 8)^3)/(s^3 + 1));
jInvariant(E2) eq -((3*(s - 2)^3*(s^3 - 78*s^2 + 84*s - 80)^3)/((s + 1)^9*(s^2 - s + 1)));


// we verify that a 3*(s^2 + 2*s - 2)-twist of E corresponds to the element of the Hesse pencil defined by s
P2<X,Y,Z>:=ProjectiveSpace(K,2);
Es:=Curve(P2, X^3 + Y^3 + Z^3 + 3*s*X*Y*Z);
Es:=EllipticCurve(Es,Es![-1,1,0]);
_,c:=IsQuadraticTwist(Es,E);
1/c * 4*(s^2 - s + 1)^4/s^6;


// we verify that a 3*(s^2 + 2*s - 2)-twist of C matches the case a=b=s from the main theorem
R<x>:=PolynomialRing(K);
a:=s; b:=s;
C:=HyperellipticCurve(
  (4*t*x^3 + 3*(t + 1)*(t + 3)*x^2 + 12*t*(t + 1)*x + 4*t*(3*t + 1))
  *(4*(3*t + 1)*x^3 + 9*(t + 1)^2*x^2 + 6*(t + 1)*(3*t + 1)*x + (3*t + 1)^2)
);
C1:=HyperellipticCurve(1/3/(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)*(
  (2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)^2*x^3
  - 3*(2*a + a^4 + 3*b^2 - 2*a*b^3)*(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)*x^2
  - 9*(-1 + a*b)*(a + b^2)*(a + 2*a^4 + 3*a^2*b + 3*b^2 - a*b^3)*x
  - (-1 + 4*a^3 + 6*a*b + 3*a^2*b^2 + 4*b^3)*(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)
  )*(
  (2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)*(-1 + 4*a^3 + 6*a*b + 3*a^2*b^2 + 4*b^3)*x^3
  - 9*(a^2 + b)*(-1 + a*b)*(-3*a^2 - b + a^3*b - 3*a*b^2 - 2*b^4)*x^2
  - 3*(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)*(-3*a^2 - 2*b + 2*a^3*b - b^4)*x
  - (2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)^2
));
C2:=HyperellipticCurve(1/3/(3*s^2 - 4*s + 2)
  *((s+1)^2*x^3 + 3*(2*s^2 - 4*s +3)*x^2 + 3*(3*s^2 - 2*s + 1)*x + 3)
  *((s+1)^2*x^3 - 3*(2*s^2 - 4*s +3)*x^2 + 3*(3*s^2 - 2*s + 1)*x - 3)
);

// The curve (3.17) is the curve from Theorem 5.6
IsIsomorphic(C1,C2) eq true;

// The curve is the correct twist
_,c:=IsQuadraticTwist(C,C1);
1/c * (s - 1)^6*(s + 1)^10*(3*s^2 - 4*s + 2)^2/(s^2 + 2*s - 2)^4;

