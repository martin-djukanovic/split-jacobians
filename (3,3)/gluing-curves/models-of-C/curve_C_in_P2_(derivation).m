K<a,b>:=FunctionField(QQ,2);
R<x> := PolynomialRing(K);
P2<X,Y,Z> := ProjectiveSpace(K,2);
P3<x1,x2,x3,x4> := ProjectiveSpace(K,3);

// Curve C given as an intersection of a cubic and a quadric in P3 (see curve_C_in_P3.m)
CC := Scheme(P3, [
   (2 - 9*a - 9*b + 9*a^2 + 9*b^2 + 24*a*b + a^3 + b^3 - 9*a^3*b - 9*a*b^3 - 24*a^2*b^2 + 9*a^3*b^2 + 9*a^2*b^3)*x2^3
   + (16 + 63*a + 63*b - 36*a^2 - 36*b^2 + 408*a*b - 19*a^3 - 19*b^3 + 189*a^2*b + 189*a*b^2 + 36*a^3*b + 36*a*b^3 + 24*a^2*b^2 - 9*a^3*b^2 - 9*a^2*b^3)*x3^3 
   + 3*(4 - 27*a - 27*b + 36*a^2 + 36*b^2 + 120*a*b - 7*a^3 - 7*b^3 - 72*a^2*b - 72*a*b^2 + 18*a^3*b + 18*a*b^3 + 24*a^2*b^2 - 9*a^3*b^2 - 9*a^2*b^3)*x2^2*x3 
   + 3*(-10 + 9*a + 9*b - 27*a^2 - 27*b^2 + 222*a*b + 13*a^3 + 13*b^3 + 9*a^2*b + 9*a*b^2 - 24*a^2*b^2 - 27*a^3*b - 27*a*b^3 + 9*a^3*b^2 + 9*a^2*b^3)*x3^2*x2
   + 9*(-2 - a - b + 3*a^2 + 3*b^2 - 2*a*b + 3*a^3 + 3*b^3 - a^2*b - a*b^2 - 8*a^2*b^2 + 3*a^3*b + 3*a*b^3 - a^2*b^3 - a^3*b^2)*x2*x4^2
   + 9*(1 + a)*(1 + b)*(a + b - a^2 - b^2 + 6*a*b + a^2*b + a*b^2)*x4^2*x3
   + 9*(b - a)*(1 + a)^2*(1 + b)^2*x4^3
   + 9*(b - a)*(1 - 2*a - 2*b + 3*a^2 + 3*b^2 + 9*a*b - 4*a^2*b - 4*a*b^2 - a^2*b^2)*x2^2*x4
   + 9*(b - a)*(1 + a)*(1 + b)*(7 + 3*a + 3*b - a*b)*x3^2*x4
   + 18*(b - a)*(5 + 5*a  + 5*b - 3*a^2 - 3*b^2 + 12*a*b + a^2*b + a*b^2 + a^2*b^2)*x2*x3*x4,
   (2 - 3*a*b + a^3 + b^3 + 3*a^2*b^2)*x1^2
   + 3*(1 - a*b)*x2^2 + 3*(1 + a)*(1 + b)*x4^2
   + 3*(7 + 3*a + 3*b - a*b)*x3^2
   + 9*(b - a)*x2*x4
   + 3*(10 - 3*a - 3*b + 2*a*b)*x2*x3
]);

/* A linear form defining a hyperplane whose intersection with C consists of two triple points.
   Another such hyperplane is obtained by exchanging a and b. Derivation is found in planes_intersecting_C.m
   Since (a^3+1)(b^3+1)(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)!=0, L0 is not identically zero.  */
L0 := - (1 - 3*a + 2*a^3 - 3*b + 3*a*b +  6*a^2*b - 3*a^3*b + 3*b^2 - 3*a^2*b^2 - b^3)*x2
      + (1 + 6*a + 2*a^3 - 3*b + 3*a*b - 12*a^2*b - 3*a^3*b - 6*b^2 - 3*a^2*b^2 - b^3)*x3
      + (1 + 2*a^3 + 3*b + 3*a*b + 3*a^3*b - 3*a^2*b^2 - b^3)*x4;
// S0 := ReducedSubscheme(C meet Scheme(P3, L0)); Degree(S0) eq 2;


/* A linear form defining a hyperplane that intersects C at the same two points, but with multiplicity 2, and two other points. */
L1 := 9*(a - b)*(1 - 2*a - 2*b + a*b)*x2 + 2*(1 + 3*a + 6*a^2 + 2*a^3 + 3*b + 3*a^2*b + 6*b^2 + 3*a*b^2 + 3*a^2*b^2 + 2*b^3)*x4;
L2 := 9*(a - b)*(1 - 2*a - 2*b + a*b)*x3 + (2 - 3*a - 6*a^2 + 4*a^3 - 3*b - 3*a^2*b - 6*b^2 - 3*a*b^2 + 6*a^2*b^2 + 4*b^3)*x4;
L3 := (L1 - L2)/9; //(a - b)*(1 - 2*a - 2*b + a*b)*(x2 - x3) + (a + b + 2*a^2 + 2*b^2 + a^2*b + a*b^2)*x4; (preferred for simplicity)
// S := ReducedSubscheme(C meet Scheme(P3, L3)); Degree(S) eq 4;

/* There are exceptions:
   1) If a=b=0 then L3=0, so use L3=x4 instead. This yields the model -6y^2=(x^3+2)(2x^3+1), given in examples.m
   2) If (-a + 2*a^2*b + b^2)*(-b + 2*a*b^2 + a^2)=0 then the quadric without x1 defining S has discriminant zero. In this case
      Z(L3) also has only two points of intersection with C. We can instead use L1 or L2.
      The only values of (a,b) for which L1,L2,L3 all intersect C at two points are:
      i) a=b=1/2
      ii) b^2 + 5*b - 2 = 0, a = (1-b)/4
      iii) a^2 + 5*a - 2 = 0, b = (1-a)/4
      
      Case i) needs to be dealt with separately.
      In case ii) we can use L3 := x2 + (3*b + 17)*x3 and in case iii) we can use L3 := x2 + (3*a + 17)*x3  */

// We now use the linear forms we've found to define a map to IP^2.
C1 := map<P3 -> P2 | [L1, x1, L0]>(CC);
C2 := map<P3 -> P2 | [L2, x1, L0]>(CC);
C3 := map<P3 -> P2 | [L3, x1, L0]>(CC);

/* This results in models of the form y^2*g(x)^2 = f(x). To simplify the models, we look for squares next to Y^2 and sixth powers next to Z^6.
   We analyze the following:
   [Factorization(Coefficient(Basis(Ideal(C))[1],Y,2)) : C in [C1,C2,C3]]; 
   [Coefficient(Basis(Ideal(C))[1],Z,6) : C in [C1,C2,C3]];   */

/* There are now two distinct cases: a^3 + 3*a*b + b^3 - 1 is either zero or it is not, i.e. g(x) is either a constant or a linear polynomial.
   We deal with the case a^3 + 3*a*b + b^3 - 1 != 0 first.  */

/***************************************
  Case 1: a^3 + 3*a*b + b^3 - 1 != 0
 ***************************************/
T1 := (a^3 + 3*a*b + b^3 - 1)*X + (-a^3 - 3*a^2*b^2 - 6*a^2 - 3*a*b^3 - 12*a*b^2 + 3*a*b - 3*a + 2*b^3 + 6*b + 1)*Z;
T2 := (a^2 + b^2 - a*b + a + b + 1)*X + (-a^2 - 3*a*b^2 + a*b + 2*a + 2*b^2 + 2*b - 1)*Z;
T3 := (a^3 + 3*a*b + b^3 - 1)*X + (-a^2 - 2*a*b^2 + b)*Z;

r1 := 2 * (a^3 + 3*a*b + b^3 - 1)^3 * (-1 - 6*a - 2*a^3 + 3*b - 3*a*b + 12*a^2*b + 3*a^3*b + 6*b^2 + 3*a^2*b^2 + b^3)^2;
r2 := 2 * (a^3 + 3*a*b + b^3 - 1)^3 * (1 - 2*a - 2*a^2 - 2*b - a*b + 3*a^2*b + b^2)^2;
r3 := 2 * (a^3 + 3*a*b + b^3 - 1)^3 * (-a + 2*a^2*b + b^2)^2;

q1 := -1 - 6*a - 2*a^3 + 3*b - 3*a*b + 12*a^2*b + 3*a^3*b + 6*b^2 + 3*a^2*b^2 + b^3;
q2 := 1 - 2*a - 2*a^2 - 2*b - a*b + 3*a^2*b + b^2;
q3 := -a + 2*a^2*b + b^2;

C1 := map<P2->P2 | [q1^2*T1*Z, r1*T1*Y, q1^3*Z^2]>(C1);
C2 := map<P2->P2 | [q2^2*T2*Z, r2*T2*Y, q2^3*Z^2]>(C2);
C3 := map<P2->P2 | [q3^2*T3*Z, r3*T3*Y, q3^3*Z^2]>(C3);

C := Scheme(P2,
	-3*(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)*Y^2*Z^4
	+ ( 
		(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)^2*X^3
		- 3*(2*a + a^4 + 3*b^2 - 2*a*b^3)*(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)*X^2*Z
		- 9*(-1 + a*b)*(a + b^2)*(a + 2*a^4 + 3*a^2*b + 3*b^2 - a*b^3)*X*Z^2
		- (-1 + 4*a^3 + 6*a*b + 3*a^2*b^2 + 4*b^3)*(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)*Z^3
	)*(
		(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)*(-1 + 4*a^3 + 6*a*b + 3*a^2*b^2 + 4*b^3)*X^3
		- 9*(a^2 + b)*(-1 + a*b)*(-3*a^2 - b + a^3*b - 3*a*b^2 - 2*b^4)*X^2*Z
		- 3*(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)*(-3*a^2 - 2*b + 2*a^3*b - b^4)*X*Z^2
		- (2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)^2*Z^3
	)
);

// We verify that the same curve is obtained for all three choices:
C1 eq C2 and C1 eq C3 and C1 eq C;


/************************************************************************
 Case 1: b^2 + 5*b - 2 = 0 and a = (1-b)/4 
 This is covered by the same formula, as is verified by the following:
************************************************************************/
R<x> := PolynomialRing(QQ);
K<b> := ext<QQ | x^2+5*x-2>;
a:=(1-b)/4;
R<x> := PolynomialRing(K);
P2<X,Y,Z> := ProjectiveSpace(K,2);
P3<x1,x2,x3,x4> := ProjectiveSpace(K,3);
CC := Scheme(P3, [
   (2 - 9*a - 9*b + 9*a^2 + 9*b^2 + 24*a*b + a^3 + b^3 - 9*a^3*b - 9*a*b^3 - 24*a^2*b^2 + 9*a^3*b^2 + 9*a^2*b^3)*x2^3
   + (16 + 63*a + 63*b - 36*a^2 - 36*b^2 + 408*a*b - 19*a^3 - 19*b^3 + 189*a^2*b + 189*a*b^2 + 36*a^3*b + 36*a*b^3 + 24*a^2*b^2 - 9*a^3*b^2 - 9*a^2*b^3)*x3^3 
   + 3*(4 - 27*a - 27*b + 36*a^2 + 36*b^2 + 120*a*b - 7*a^3 - 7*b^3 - 72*a^2*b - 72*a*b^2 + 18*a^3*b + 18*a*b^3 + 24*a^2*b^2 - 9*a^3*b^2 - 9*a^2*b^3)*x2^2*x3 
   + 3*(-10 + 9*a + 9*b - 27*a^2 - 27*b^2 + 222*a*b + 13*a^3 + 13*b^3 + 9*a^2*b + 9*a*b^2 - 24*a^2*b^2 - 27*a^3*b - 27*a*b^3 + 9*a^3*b^2 + 9*a^2*b^3)*x3^2*x2
   + 9*(-2 - a - b + 3*a^2 + 3*b^2 - 2*a*b + 3*a^3 + 3*b^3 - a^2*b - a*b^2 - 8*a^2*b^2 + 3*a^3*b + 3*a*b^3 - a^2*b^3 - a^3*b^2)*x2*x4^2
   + 9*(1 + a)*(1 + b)*(a + b - a^2 - b^2 + 6*a*b + a^2*b + a*b^2)*x4^2*x3
   + 9*(b - a)*(1 + a)^2*(1 + b)^2*x4^3
   + 9*(b - a)*(1 - 2*a - 2*b + 3*a^2 + 3*b^2 + 9*a*b - 4*a^2*b - 4*a*b^2 - a^2*b^2)*x2^2*x4
   + 9*(b - a)*(1 + a)*(1 + b)*(7 + 3*a + 3*b - a*b)*x3^2*x4
   + 18*(b - a)*(5 + 5*a  + 5*b - 3*a^2 - 3*b^2 + 12*a*b + a^2*b + a*b^2 + a^2*b^2)*x2*x3*x4,
   (2 - 3*a*b + a^3 + b^3 + 3*a^2*b^2)*x1^2
   + 3*(1 - a*b)*x2^2 + 3*(1 + a)*(1 + b)*x4^2
   + 3*(7 + 3*a + 3*b - a*b)*x3^2
   + 9*(b - a)*x2*x4
   + 3*(10 - 3*a - 3*b + 2*a*b)*x2*x3
]);
L0 := (-1 + 3*a - 2*a^3 + 3*b - 3*a*b - 6*a^2*b + 3*a^3*b - 3*b^2 + 3*a^2*b^2 + b^3)*x2 + (1 + 6*a + 2*a^3 - 3*b + 3*a*b - 12*a^2*b - 3*a^3*b - 6*b^2 - 3*a^2*b^2 - b^3)*x3 + (1 + 2*a^3 + 3*b + 3*a*b + 3*a^3*b - 3*a^2*b^2 - b^3)*x4;
L1 := x2 + (3*b + 17)*x3;
C := map<P3 -> P2 | [L1, x1, L0]>(CC);  
T := X + 1/162*(-155*b - 830)*Z;
d := b^2*(b+5)*(2*b-1)^2;
C := map<P2->P2 | [dd*T*Z, 1/3/(8*b-3)^3 * d^3 * (1-2*b)*b^3*T*Y, Z^2 ]>(C); // (8*b+43)*(8*b-3) = -1.
// This curve is isomorphic to the curve given by the general formula when a^3 + 3*a*b + b^3 - 1 is not zero.




/***************************************
  Case 2: a^3 + 3*a*b + b^3 - 1 != 0
 ***************************************
  a^3 + 3*a*b + b^3 - 1 = 0 splits over K(w) with 1 + w + w^2 = 0.
  One of the following holds:
  i)   a + b = 1
  ii)  a*w + b*w^2 = 1
  iii) a*w^2 + b*w = 1
  Cases ii) and iii) clearly give isomorphic curves so it suffices to treat only one of them.
****************************************/

/**********************
 Case 2i: a + b = 1
***********************/
K<a>:=FunctionField(QQ);
R<x>:=PolynomialRing(K);
P2<X,Y,Z> := ProjectiveSpace(K,2);
P3<x1,x2,x3,x4> := ProjectiveSpace(K,3);

// Substituting b:=1-a gives the following model for C in IP^3:
CC := Scheme(P3, [
   (3*a^4 - 6*a^3 + 9*a^2 - 6*a + 3)*x2^3
   + (-57*a^4 + 114*a^3 - 819*a^2 + 762*a + 24)*x3^3 
   + 3*(-21*a^4 + 42*a^3 - 36*a^2 + 15*a + 6)*x2^2*x3 
   + 3*(39*a^4 - 78*a^3 - 180*a^2 + 219*a - 15)*x3^2*x2
   + 9*(-15*a^4 + 30*a^3 - 15*a + 3)*x2*x4^2
   + 9*(1 + a)*(2 - a)*(-9*a^2 + 9*a)*x4^2*x3
   + 9*(1 - 2*a)*(1 + a)^2*(2 - a)^2*x4^3
   + 9*(1 - 2*a)*(-a^4 + 2*a^3 - a + 2)*x2^2*x4
   + 9*(1 - 2*a)*(1 + a)*(2 - a)*(a^2 - a + 10)*x3^2*x4
   + 18*(1 - 2*a)*(a^4 - 2*a^3 - 18*a^2 + 19*a + 7)*x2*x3*x4,
   (3*a^4 - 6*a^3 + 9*a^2 - 6*a + 3)*x1^2
   + 3*(a^2 - a + 1)*x2^2 + 3*(1 + a)*(2 - a)*x4^2
   + 3*(a^2 - a + 10)*x3^2
   + 9*(1 - 2*a)*x2*x4
   + 3*(-2*a^2 + 2*a + 7)*x2*x3
]);

L0 := (1 + 2*a - 2*a^2)*x4 + 3*(2*a - 1)*x3; // S0 := ReducedSubscheme(CC meet Scheme(P3,L0)); Degree(S0) eq 2;

/* This linear form is not identically zero. However, it defines the same plane as L0 if a=b=1/2,
   so that case needs to be treated separately. */
L1 := (2*a - 1)*(x2-x3) - 3*x4;  // S := ReducedSubscheme(CC meet Scheme(P3,L1)); Degree(S) eq 4;
C := map<P3 -> P2 | [L1, 6*(2*a - 1)^3*(1 - a + a^2)*x1, L0]>(CC);
C eq Scheme(P2, -Y^2*Z^4 +
      ((a^2 - a + 1)^2*X^3 - 6*(a - 1)*(a^3 + 1)*X^2*Z + 3*(a - 2)*(4*a^2 - a - 2)*X*Z^2 - 6*(a^2 + 2*a - 2)*Z^3)*
      ((a^2 - a + 1)^2*X^3 - 6*a*(a - 2)*(a^2 - a + 1)*X^2*Z - 3*(a + 1)*(4*a^2 - 7*a + 1)*X*Z^2 - 6*(a^2 - 4*a + 1)*Z^3)
);


/**********************
 Case 2i: a = b = 1/2
***********************/
K := Rationals();
P2<X,Y,Z> := ProjectiveSpace(K,2);
P3<x1,x2,x3,x4> := ProjectiveSpace(K,3);
a := 1/2; b := 1/2;
CC := Scheme(P3,[
  x2^3 + 15*x2^2*x3 + 75*x2*x3^2 + 125*x3^3 - 9*x2*x4^2 + 27*x3*x4^2,
  3*x1^2 + 4*x2^2 + 40*x2*x3 + 52*x3^2 + 12*x4^2
]);
C := map<P3 -> P2 | [x2 + 5*x3, 18*x1, x4]>(CC);
C eq Scheme(P2, -Y^2*Z^4 + (X^3 + 6*X^2*Z + 9*X*Z^2 + 36*Z^3)*(X^3 - 6*X^2*Z + 9*X*Z^2 - 36*Z^3));


/**************************
 Case 2ii: a*w + b*w^2 = 1
***************************/
R<x> := PolynomialRing(QQ);
K<w> := ext<QQ | 1+x+x^2>;
K<a> := FunctionField(K);
R<A> := PolynomialRing(K);
h := hom<K->R | A>;
P2<X,Y,Z> := ProjectiveSpace(K,2);
P3<x1,x2,x3,x4> := ProjectiveSpace(K,3);

// Substituting b := w - w^2*a gives the following model for C in IP^3:
CC := Scheme(P3, [
  ((9*w - 9)*a^5 + (-60*w - 45)*a^4 + (-18*w + 66)*a^3 + (81*w + 63)*a^2 + (12*w - 45)*a - 18*w -6)*x2^3 + ((-27*w + 27)*a^5 + (207*w + 135)*a^4 + (-432*w - 495)*a^3 + (81*w + 864)*a^2 +(558*w - 108)*a - 189*w - 117)*x2^2*x3 + ((27*w - 27)*a^5 + (-234*w - 135)*a^4 + (108*w +387)*a^3 + (810*w + 513)*a^2 + (549*w + 108)*a + (108*w + 90))*x2*x3^2 + ((-9*w + 9)*a^5 +(87*w + 45)*a^4 + (342*w + 42)*a^3 + (486*w + 18)*a^2 + (339*w + 45)*a + (99*w + 33))*x3^3 +((9*w + 9)*a^5 + (63*w + 81)*a^4 + (162*w - 9)*a^3 + (-45*w - 180)*a^2 + (-126*w - 54)*a +(27*w + 45))*x2^2*x4 + ((-18*w - 18)*a^5 + (-72*w - 54)*a^4 + (-108*w - 198)*a^3 + (-72*w -450)*a^2 + (-18*w - 432)*a - 144)*x2*x3*x4 + ((9*w + 9)*a^5 + (9*w - 27)*a^4 + (-54*w -198)*a^3 + (-126*w - 342)*a^2 + (-99*w - 243)*a - 27*w - 63)*x3^2*x4 + ((-9*w + 9)*a^5 +(-18*w + 45)*a^4 + (-36*w + 63)*a^3 + (-90*w + 9)*a^2 + (-99*w - 36)*a - 36*w - 18)*x2*x4^2+ ((9*w - 9)*a^5 + (45*w - 45)*a^4 + (90*w - 90)*a^3 + (90*w - 90)*a^2 + (45*w - 45)*a +(9*w - 9))*x3*x4^2 + ((-9*w - 9)*a^5 + (-45*w - 45)*a^4 + (-90*w - 90)*a^3 + (-90*w -90)*a^2 + (-45*w - 45)*a - 9*w - 9)*x4^3,
  (3*w*a^4 - 6*a^3 + (-9*w - 9)*a^2 - 6*w*a + 3)*x1^2 + ((-3*w - 3)*a^2 - 3*w*a + 3)*x2^2 + ((6*w+ 6)*a^2 + (-3*w - 18)*a - 9*w + 30)*x2*x3 + ((-3*w - 3)*a^2 + (6*w + 18)*a + (9*w +21))*x3^2 + (9*w*a + 9*w)*x2*x4 + ((3*w + 3)*a^2 + (6*w + 6)*a + (3*w + 3))*x4^2
]);
L0 := 3*(a+w)^2*x2 - 3*(a + 1)^2*x3 - (1+2*w)*(1 + a)^2*x4;
// S0 := ReducedSubscheme(CC meet Scheme(P3,L0)); Degree(S0) eq 2;

L1 := (a + (2*w - 1))*(x2 - x3) + (2*w + 1)(a + 1)*x4;
// S := ReducedSubscheme(CC meet Scheme(P3,L1)); Degree(S);

/* Similarly to a + b = 1, the scheme S will have too few points if a = 1/2*w^2 and b = 1/2*w, so this case needs to considered separately.
*/
C := map<P3 -> P2 | [ (2*w + 1) * (a + 1) * (a + w) * L1, 2 * (2*w + 1)^3 * (a + 1)^2 * (a + w)^2 * w^2 * (2*a - w^2)^3 * x1, L0] >(CC);
C eq Scheme(P2, -Y^2*Z^4 +
              (X^3 - 6*w*(a^2 - w)*X^2*Z + 3*w*(4*a^3 -9*w^2*a^2 + 4)*X*Z^2 - 6*w*(a^2 + 2*a*w^2 - 2*w)*(a + 1)*(a + w)*Z^3)
              *(X^3 - 6*a*(a*w - 2)*X^2*Z - 3*w*(4*a^3 - 3*a^2*w^2 - 6*a*w + 1)*X*Z^2 - 6*w*(a + 1)*(a + w)*(a^2- 4*a*w^2 + w)*Z^3)
           );


/***************************************
 Case 2ii: a = 1/2*w^2 and b = 1/2*w
****************************************/
R<x> := PolynomialRing(QQ);
K<w> := ext<QQ | 1+x+x^2>;
P2<X,Y,Z> := ProjectiveSpace(K,2);
P3<x1,x2,x3,x4> := ProjectiveSpace(K,3);

// Substituting a := 1/2*w^2 and b := 1/2*w gives the following model for C in IP^3:
CC := Scheme(P3,[
    297*x2^3 + 4455*x2^2*x3 + 4779*x2*x3^2 + 2133*x3^3 + (1134*w + 567)*x2^2*x4 + (3564*w + 1782)*x2*x3*x4 + (1134*w + 567)*x3^2*x4 - 729*x2*x4^2 + 243*x3*x4^2 + (162*w + 81)*x4^3,
    27*x1^2 + 36*x2^2 + 576*x2*x3 + 252*x3^2 + (144*w + 72)*x2*x4 + 36*x4^2
]);
L0 := (2*w + 1)*(x2 - x3) + x4;
L1 := 2*x2 + x3;
C := map<P3 -> P2 | [4*L1, 12*x1, L0]>(CC);
C := map<P2 -> P2 | [ X + (1 + 2*w)*Z, Y, (1 + 2*w)*Z ]>(C);
C eq Scheme(P2, -Y^2*Z^4 + X^6 + 6*X^4*Z^2 - 39*X^2*Z^4 + 48*Z^6);
// This is isomorphic to Y^2*Z^4 = (X^3 + 6*X^2*Z + 9*X*Z^2 + 36*Z^3)*(X^3 - 6*X^2*Z + 9*X*Z^2 - 36*Z^3) over K(w).
