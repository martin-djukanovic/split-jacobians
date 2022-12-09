/* 
   --  w is a primitive 3rd root of 1, i.e. 1 + w + w^2 = 0
   
   --  E1: x^3 + y^3 + z^3 + 3*a*x*y*z = 0 and E2: x^3 + y^3 + z^3 + 3*b*x*y*z = 0 are elliptic curves with identity [-1:1:0]
   
   --  A=E1 x E2, embedded in IP^8
   
   --  G = the subgroup of A[3] that is the graph of the isomorphism E1[3] -> E2[3] defined by [-1:0:1] -> [-1:0:1] and [-w:1:0] -> [-w^2:1:0]
   
   --  Assuming 3 a^2 b^2 + a^3 + b^3 - 3 a b + 2 is non-zero, A/G is a Jac(C).
*/

K<a,b>:=FunctionField(QQ,2);
P8<X1,X2,X3,X4,X5,X6,X7,X8,X9> := ProjectiveSpace(K,8);
P3<X,Y,Z,W> := ProjectiveSpace(K,3);

A := Scheme(P8, [
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
  X2*X4 - X1*X5
]);

// The Kummer surface of the Jacobian A/G
Kum:=Scheme(P3,
    (8*a^3 + 12*a^2*b^2 + 8*b^3 + 4)*X^4
  + (12*a^2 + 24*a*b^2 + 12*b^4)*X^3*Y
  + (-3*a^4 - 18*a^3*b^2 - 27*a^2*b^4 + 24*a*b^3 + 12*a)*X^2*Y^2
  + (-2*a^3 - 12*a^2*b^2 - 18*a*b^4 + 16*b^3 + 8)*X*Y^3
  + (-3*a^2 - 6*a*b^2 - 3*b^4)*Y^4
  + (12*a^4 + 24*a^2*b + 12*b^2)*X^3*Z
  + (12*a^3 + 36*a*b + 12*b^3 - 12)*X^2*Y*Z
  + (-18*a^3*b - 18*a^2*b^3 + 18*a^2 + 18*a*b^2)*X*Y^2*Z
  + (-6*a^2*b - 6*a*b^3 + 6*a + 6*b^2)*Y^3*Z
  + (-27*a^4*b^2 + 24*a^3*b - 18*a^2*b^3 - 3*b^4 + 12*b)*X^2*Z^2
  + (-18*a^3*b^2 + 18*a^2*b - 18*a*b^3 + 18*b^2)*X*Y*Z^2
  + (-6*a^3 - 9*a^2*b^2 - 6*b^3 - 3)*Y^2*Z^2
  + (-18*a^4*b + 16*a^3 - 12*a^2*b^2 - 2*b^3 + 8)*X*Z^3
  + (-6*a^3*b + 6*a^2 - 6*a*b^2 + 6*b)*Y*Z^3
  + (-3*a^4 - 6*a^2*b - 3*b^2)*Z^4
  + (4*a^3 + 12*a*b + 4*b^3 - 4)*X^3*W
  + (-18*a^3*b - 18*a^2*b^3 + 18*a^2 + 18*a*b^2)*X^2*Y*W
  + (-18*a^2*b - 18*a*b^3 + 18*a + 18*b^2)*X*Y^2*W
  + (-4*a^3 - 12*a*b - 4*b^3 + 4)*Y^3*W
  + (-18*a^3*b^2 + 18*a^2*b - 18*a*b^3 + 18*b^2)*X^2*Z*W
  + (-9*a^4*b + 27*a^3*b^3 + 12*a^3 - 63*a^2*b^2 - 9*a*b^4 + 36*a*b + 12*b^3 + 6)*X*Y*Z*W
  + (-3*a^3*b + 9*a^2*b^3 - 27*a*b^2 - 3*b^4 + 12*b)*Y^2*Z*W
  + (-18*a^3*b + 18*a^2 - 18*a*b^2 + 18*b)*X*Z^2*W
  + (-3*a^4 + 9*a^3*b^2 - 27*a^2*b - 3*a*b^3 + 12*a)*Y*Z^2*W
  + (-4*a^3 - 12*a*b - 4*b^3 + 4)*Z^3*W
  + (-6*a^3 - 9*a^2*b^2 - 6*b^3 - 3)*X^2*W^2
  + (-3*a^3*b + 9*a^2*b^3 - 27*a*b^2 - 3*b^4 + 12*b)*X*Y*W^2
  + (9*a^3*b^2 - 9*a^2*b + 9*a*b^3 - 9*b^2)*Y^2*W^2
  + (-3*a^4 + 9*a^3*b^2 - 27*a^2*b - 3*a*b^3 + 12*a)*X*Z*W^2
  + (-3*a^3 + 9*a^2*b^2 - 27*a*b - 3*b^3 + 12)*Y*Z*W^2
  + (9*a^3*b + 9*a^2*b^3 - 9*a^2 - 9*a*b^2)*Z^2*W^2
  + (-a^3 + 3*a^2*b^2 - 9*a*b - b^3 + 4)*X*W^3
  + (6*a^3*b - 6*a^2 + 6*a*b^2 - 6*b)*Y*W^3
  + (6*a^2*b + 6*a*b^3 - 6*a - 6*b^2)*Z*W^3
  + (a^3 + 3*a*b + b^3 - 1)*W^4
);

// the composition of the isogeny f:A --> A/G=J and the quotient map J --> J/[-1]
q := map< P8 -> P3 | [ X2*X4 + X3*X7 + X6*X8, X2*X3 + X4*X6 + X7*X8, X2*X8 + X3*X6 + X4*X7, X1^2 + X5^2 + X9^2 ]>;
q1 := map< A -> Kum | [ X2*X4 + X3*X7 + X6*X8, X2*X3 + X4*X6 + X7*X8, X2*X8 + X3*X6 + X4*X7, X1^2 + X5^2 + X9^2 ]>;

// the effective and symmetric divisor on A that is invariant under translation by the points of G
D := Scheme(P8, [ X1 + X5 + X9 ]) meet A;

// the conic in the Kummer surface that is the image of D under q, of which the genus-2 curve C=f(D) is a double cover
H:= Kum meet Scheme(P3, 2*X + W);
q2 := map< D -> H | [ X2*X4 + X3*X7 + X6*X8, X2*X3 + X4*X6 + X7*X8, X2*X8 + X3*X6 + X4*X7, X1^2 + X5^2 + X9^2 ]>;

// the six points of order two in A[2] that lie on D
E12 := Scheme(P8, [ 2*X5^3 + 3*a*X5^2*X8 + X8^3, X1 + X5, X2 - X5, X3, X4 + X5, X6, X7 + X8, X9 ]);
E22 := Scheme(P8, [ 2*X5^3 + 3*b*X5^2*X6 + X6^3, X1 + X5, X2 + X5, X3 + X6, X4 - X5, X7, X8, X9 ]);

// the branch locus of the double cover C --> H, from which the (geometric) isomorphism class of C can be recovered
B := q(Union(E12,E22));
