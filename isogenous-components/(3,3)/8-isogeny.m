K<t>:=FunctionField(QQ);
A2<x,y>:=AffineSpace(K,2);
R<X>:=PolynomialRing(K);
h:=hom<CoordinateRing(A2)->R|[X,0]>;

// the genus-2 curve
//C := Curve(A2, -y^2 +  4*t*(2*t + 1)*x^6 - (8*t^4 + 4*t^3 - 2*t^2 - 7*t - 1)*x^4 - (2*t^4 + 7*t^3 + t^2 - t - 1)*x^2 - t^2*(t + 1));
C := Curve(A2, -y^2 + (x - t)*(x + t)*(1 + x^2 + 2*t*x^2)*(1 + t + 4*t*x^2));

// degree-3 coverings
E1 := Curve(A2, -y^2 + x^3 - (2*(-2 + t - 2*t^2 - 27*t^3 + 2*t^4)*x^2)/(1 - t + 2*t^2) - 
  ((1 + 2*t)*(-5 - 2*t - 94*t^2 - 104*t^3 + 179*t^4 - 494*t^5 + 88*t^6)*x)/(1 - t + 2*t^2)^2 - 
  (2*(-1 + t)^3*(1 + 2*t)^2*(1 + 5*t)^3)/(1 - t + 2*t^2)^2
);
E2:=Curve(A2, -y^2 + x^3 - (16*t^4 - 4*t^3 + 4*t^2 + 27*t - 1)/(2*t^2 - t + 1)*x^2 + (t*(t + 1)*(80*t^6 + 16*t^5 + 376*t^4 + 208*t^3 - 179*t^2 + 247*t - 22))/(2*t^2 - t + 1)^2*x - t^2*(t + 1)^2*(2*t - 1)^3*(2*t + 5)^3/(2*t^2 - t + 1)^2);
f1 := map<C->E1|[
	(2*t + 1)*(x - 1)^2*(4*t^2*x + t^2 - t*x - 3*t - x) / ((x + t)*(2*t*x^2 + x^2 + 1)), 
	2*(t + 1)^3*(2*t + 1)/(2*t^2 - t + 1) * y*(2*t*x - x - 1) * (2*t*x^2 + 2*t*x + t + x^2) / ((x + t)^2*(2*t*x^2 + x^2 + 1)^2)
]>;
f2 := map<C->E2|[
	-(t + 1) * t * (2*x + 1)^2 * (2*t^2 - 6*t*x + t + x - 2)/((x - t)*(4*t*x^2 + t + 1)),
	2*t*(2*t + 1)^3*(t + 1)/(2*t^2 - t + 1) * y * (2*t*x - t + 1)*(t + 2*x^2 - 2*x + 1)/((x - t)^2*(4*t*x^2 + t + 1)^2)
]>;

// degree-2 coverings
E3 := Curve(A2, -y^2 + x^3 - (8*t^4 + 4*t^3 - 2*t^2 - 7*t - 1)/(16*t^2*(2*t + 1)^2)*x^2 - (2*t^4 + 7*t^3 + t^2 - t - 1)/(64*t^3*(2*t + 1)^3)*x - (t + 1)/(256*t^2*(2*t + 1)^4));
E4 := Curve(A2, -y^2 + x^3 - (2*t^4 + 7*t^3 + t^2 - t - 1)/(t^4*(t + 1)^2)*x^2 + (8*t^4 + 4*t^3 - 2*t^2 - 7*t - 1)/(t^6*(t + 1)^3)*x + 4*(2*t + 1)/(t^7*(t + 1)^4));
f3 := map<C->E3|[ x^2/(4*t*(2*t + 1)), y/(4*t*(2*t + 1))^2 ]>;
f4 := map<C->E4|[ -1/(t^2*(t + 1))/x^2, 1/(t^2*(t + 1))^2*y/x^3 ]>;


E:=[EllipticCurve(h(Basis(Ideal(e))[1])) : e in [E1,E2,E3,E4]];
j:=[jInvariant(e) : e in E];
D1:=Factorization(DivisionPolynomial(E[1],2))[1][1];
D2:=Factorization(DivisionPolynomial(E[2],2))[1][1];
D3:=Factorization(DivisionPolynomial(E[3],2))[2][1];
D4:=Factorization(DivisionPolynomial(E[4],2))[2][1];

F:=IsogenyFromKernel(E[1],D1); IsIsomorphic(F,E[3]);
F:=IsogenyFromKernel(E[3],D3); IsIsomorphic(F,E[4]);
F:=IsogenyFromKernel(E[4],D4); IsIsomorphic(F,E[2]);

// The 8-isogeny E1->E2 is the composition of 2-isogenies E1->E3->E4->E2

j eq [
	-4*(16*t^4 + 32*t^3 - 40*t^2 - 56*t + 1)^3/(t*(t + 1)*(2*t + 1)^8),
	-16*(t^4 - 28*t^3 - 10*t^2 + 4*t + 1)^3/(t^2*(t + 1)^8*(2*t + 1)), 
	16*(16*t^4 + 32*t^3 + 20*t^2 + 4*t + 1)^3/(t^2*(t + 1)^2*(2*t + 1)^4), 
	256*(t^4 + 2*t^3 + 5*t^2 + 4*t + 1)^3/(t^4*(t + 1)^4*(2*t + 1)^2)
];
