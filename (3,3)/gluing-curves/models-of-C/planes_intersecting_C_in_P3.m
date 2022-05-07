/* A model of C in P3 is an intersection of a cubic and a quadric. We are looking for p and q such that x4 = p*x2 + q*x3 leads to a cubic
   with two triple roots. */
   
QQ := Rationals();
K<a,b>:=FunctionField(QQ,2);
R<x2,x3,x4,p,q>:=PolynomialRing(K,5);
cubic:=func<x2,x3,x4 | (2 - 9*a - 9*b + 9*a^2 + 9*b^2 + 24*a*b + a^3 + b^3 - 9*a^3*b - 9*a*b^3 - 24*a^2*b^2 + 9*a^3*b^2 + 9*a^2*b^3)*x2^3
   + (16 + 63*a + 63*b - 36*a^2 - 36*b^2 + 408*a*b - 19*a^3 - 19*b^3 + 189*a^2*b + 189*a*b^2 + 36*a^3*b + 36*a*b^3 + 24*a^2*b^2 - 9*a^3*b^2 - 9*a^2*b^3)*x3^3 
   + 3*(4 - 27*a - 27*b + 36*a^2 + 36*b^2 + 120*a*b - 7*a^3 - 7*b^3 - 72*a^2*b - 72*a*b^2 + 18*a^3*b + 18*a*b^3 + 24*a^2*b^2 - 9*a^3*b^2 - 9*a^2*b^3)*x2^2*x3 
   + 3*(-10 + 9*a + 9*b - 27*a^2 - 27*b^2 + 222*a*b + 13*a^3 + 13*b^3 + 9*a^2*b + 9*a*b^2 - 24*a^2*b^2 - 27*a^3*b - 27*a*b^3 + 9*a^3*b^2 + 9*a^2*b^3)*x3^2*x2
   + 9*(-2 - a - b + 3*a^2 + 3*b^2 - 2*a*b + 3*a^3 + 3*b^3 - a^2*b - a*b^2 - 8*a^2*b^2 + 3*a^3*b + 3*a*b^3 - a^2*b^3 - a^3*b^2)*x2*x4^2
   + 9*(1 + a)*(1 + b)*(a + b - a^2 - b^2 + 6*a*b + a^2*b + a*b^2)*x4^2*x3
   + 9*(b - a)*(1 + a)^2*(1 + b)^2*x4^3
   + 9*(b - a)*(1 - 2*a - 2*b + 3*a^2 + 3*b^2 + 9*a*b - 4*a^2*b - 4*a*b^2 - a^2*b^2)*x2^2*x4
   + 9*(b - a)*(1 + a)*(1 + b)*(7 + 3*a + 3*b - a*b)*x3^2*x4
   + 18*(b - a)*(5 + 5*a  + 5*b - 3*a^2 - 3*b^2 + 12*a*b + a^2*b + a*b^2 + a^2*b^2)*x2*x3*x4>;
quadric:=func<x1,x2,x3,x4 | (2 - 3*a*b + a^3 + b^3 + 3*a^2*b^2)*x1^2
   + 3*(1 - a*b)*x2^2 + 3*(1 + a)*(1 + b)*x4^2
   + 3*(7 + 3*a + 3*b - a*b)*x3^2
   + 9*(b - a)*x2*x4
   + 3*(10 - 3*a - 3*b + 2*a*b)*x2*x3>;
C := cubic(x2,x3,p*x2+q*x3);
d:=Quotrem(Discriminant(C,x2),x3^6);
eq1:=Factorization(d)[1][1];
P:=p - GroebnerBasis(ideal<R|eq1>)[1];
C := cubic(x2, x3, P*x2 + q*x3);
d:=Quotrem(Discriminant(Derivative(C,x2),x2),x3^2);
eq2:=Factorization(d)[1][1];
d:=Quotrem(Discriminant(Derivative(C,x3),x3),x2^2);
eq3:=Factorization(d)[1][1];
Q:=K!(q - GroebnerBasis(ideal<R|eq2,eq3>)[1]);
P:=K!(p-GroebnerBasis(ideal<R| p - P, q - Q>)[1]);


// Having found L0, we determine the two points of intersection of C and the zero locus of L0.
// This gives us equations of planes that intersect C at these two points (with multiplicity 2) and also (two) additional points.
P3<x1,x2,x3,x4> := ProjectiveSpace(K,3);
L0:= -x4 + P*x2 + Q*x3;
C:=Scheme(P3, [cubic(x2,x3,x4), quadric(x1,x2,x3,x4)]);
S:=ReducedSubscheme(C meet Scheme(P3, L0));
// The first equation contains x1^2 so that is not the one we want. Having found these, we can take various linear combinations of L0,L1,L2
// We also need to clear the denominators and deal with cases of (a,b) for which they are zero.
L1:=Basis(Ideal(S))[2];
L2:=Basis(Ideal(S))[3];
