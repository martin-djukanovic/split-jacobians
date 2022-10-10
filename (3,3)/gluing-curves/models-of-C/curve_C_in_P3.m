R<x> := PolynomialRing(QQ);
K<w> := ext<QQ|1+x+x^2>;
R<x> := PolynomialRing(K);
K<a,b>:=FunctionField(K,2);
P2<X,Y,Z> := ProjectiveSpace(K,2);
P8<X1,X2,X3,X4,X5,X6,X7,X8,X9> := ProjectiveSpace(K,8);
P3<x1,x2,x3,x4> := ProjectiveSpace(K,3);

D := func<P|Scheme(P8, [
	X3^3 + X6^3 + X9^3 + 3*a*X3*X6*X9,
	X2^3 + X5^3 + X8^3 + 3*a*X2*X5*X8,
	X1^3 + X4^3 + X7^3 + 3*a*X1*X4*X7,
	X7^3 + X8^3 + X9^3 + 3*b*X7*X8*X9,
	X4^3 + X5^3 + X6^3 + 3*b*X4*X5*X6,
	X1^3 + X2^3 + X3^3 + 3*b*X1*X2*X3,
	X6*X8 - X5*X9,
	X3*X8 - X2*X9,
	X6*X7 - X4*X9,
	X5*X7 - X4*X8,
	X3*X7 - X1*X9,
	X2*X7 - X1*X8,
	X3*X5 - X2*X6,
	X3*X4 - X1*X6,
	X2*X4 - X1*X5,
	P
])>;

// This model of C is the intersection of a cubic F(x2,x3,x4) = 0 and a quadric x1^2 = G(x2,x3,x4). 
// The hyperelliptic involution is given by x1 --> -x1.
// Replacing (a,b) by (b,a) gives an isomorphic curve (via x4 --> -x4).
C:=Scheme(P3, [
  // cubic
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
  
  // quadric
   (2 - 3*a*b + a^3 + b^3 + 3*a^2*b^2)*x1^2
   + 3*(1 - a*b)*x2^2
   + 3*(1 + a)*(1 + b)*x4^2
   + 3*(7 + 3*a + 3*b - a*b)*x3^2
   + 9*(b - a)*x2*x4
   + 3*(10 - 3*a - 3*b + 2*a*b)*x2*x3
]);

// The (3,3)-isogeny E1 x E2 --> Jac(C), restricted to D, followed by an isomorphism.
// Note that f is defined over Q and does not depend on a and b. This allowed us to determine C relatively easily, by interpolation.
f:=map<D(X1+X5+X9) -> C | [
	2*((w*X1 + w^2*X5 + X9)^3 + (w^2*X1 + w*X5 + X9)^3),
	2*((X3 + X4 + X8)^3 - (X2 + X6 + X7)^3),
	(w*X3 + w^2*X4 + X8)^3 - (w^2*X2 + w*X6 + X7)^3 + (w^2*X3 + w*X4 + X8)^3 - (w*X2 + w^2*X6 + X7)^3,
	3/(w-w^2)*((w*X3 + w^2*X4 + X8)^3-(w^2*X2 + w*X6 + X7)^3 - (w^2*X3 + w*X4 + X8)^3 + (w*X2 + w^2*X6 + X7)^3)
]>;

// When gluing along the E1[3]-->E2[3] determined by S |--> -S and T |--> -T we similarly have
g:=map<D(X2+X4+X9) -> C | [
	2*((w*X2 + w^2*X4 + X9)^3 + (w^2*X2 + w*X4 + X9)^3),
	2*((X3 + X5 + X7)^3 - (X1 + X6 + X8)^3),
	(w*X3 + w^2*X5 + X7)^3 - (w^2*X1 + w*X6 + X8)^3 + (w^2*X3 + w*X5 + X7)^3 - (w*X1 + w^2*X6 + X8)^3,
	3/(w-w^2)*((w*X3 + w^2*X5 + X7)^3-(w^2*X1 + w*X6 + X8)^3 - (w^2*X3 + w*X5 + X7)^3 + (w*X1 + w^2*X6 + X8)^3)
]>;


/****************************************************************************************************************************
   Where this map comes from: E1 x E2 --> (E1 x E2)/G is defined by the cubes of the linear forms that define
   the hyperplanes that are invariant under translation by the points of G. These are:
  (w*X1 + w^2*X5 + X9)^3, (w^2*X1 + w*X5 + X9)^3, (X3 + X4 + X8)^3, (X2 + X6 + X7)^3, (w*X3 + w^2*X4 + X8)^3
  (w^2*X2 + w*X6 + X7)^3, (w^2*X3 + w*X4 + X8)^3, (w*X2 + w^2*X6 + X7)^3, (X1 + X5 + X9)^3
  Applying a suitable isomorphism and projecting to IP^3 leaves us with the definition of f above;
  e.g. 
  isog:=map<P8->P8|[
        // these four give hyperplanes
	(X1 + X5 + X9)^3,
	((X3 + X4 + X8)^3 + (X2 + X6 + X7)^3),
	1/(w-w^2)*((w*X3 + w^2*X4 + X8)^3 - (w^2*X2 + w*X6 + X7)^3 - (w^2*X3 + w*X4 + X8)^3 + (w*X2 + w^2*X6 + X7)^3),
	1/(w-w^2)*((w*X3 + w^2*X4 + X8)^3 - (w^2*X3 + w*X4 + X8)^3 + (w^2*X2 + w*X6 + X7)^3 - (w*X2 + w^2*X6 + X7)^3),
	1/(w-w^2)*((w*X1 + w^2*X5 + X9)^3 - (w^2*X1 + w*X5 + X9)^3),
	
	// these five give four quadrics
	((w*X1 + w^2*X5 + X9)^3 + (w^2*X1 + w*X5 + X9)^3),
	((X3 + X4 + X8)^3 - (X2 + X6 + X7)^3),
	(w*X3 + w^2*X4 + X8)^3 - (w^2*X2 + w*X6 + X7)^3 + (w^2*X3 + w*X4 + X8)^3 - (w*X2 + w^2*X6 + X7)^3,
	1/(w-w^2)*((w*X3 + w^2*X4 + X8)^3 - (w^2*X3 + w*X4 + X8)^3 - (w^2*X2 + w*X6 + X7)^3 + (w*X2 + w^2*X6 + X7)^3)
  ]>;
  Dropping the first five coordinates gives the intersection of a cubic and a quadric in P3, which is birational to isog(D).
****************************************************************************************************************************/
 
