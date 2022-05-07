R<T,X1,X2,X3,X4,X5,X6,X7,X8,X9,a,b> := PolynomialRing(QQ, 12);
s := 3*a;
t := 3*b;

I := ideal < R | [
  // equations that define the nine points of A[2] that are not in the image of the theta divisor "E1 + E2"
  4*X5^3 - s*t*X5^2*X9 - s*X6^2*X9 - t*X8^2*X9 - X9^3,
  2*X5^2*X6 + s*X5^2*X9 + X8^2*X9,
  2*X5*X6^2 + s*X5*X6*X9 + X8*X9^2,
  2*X6^3 + s*X6^2*X9 + X9^3,
  2*X5^2*X8 + t*X5^2*X9 + X6^2*X9,
  2*X5*X8^2 + t*X5*X8*X9 + X6*X9^2,
  2*X8^3 + t*X8^2*X9 + X9^3,
  X6*X8 - X5*X9,
  X1 - X5,
  X2 - X5,
  X3 - X6,
  X4 - X5,
  X7 - X8,
  // equation that defines the effective divisor D, that is linearly equivalent to E1+E2, and fixed by [-1] and translation by A[3]
  X1 + X5 + X9,
  // dehomogenize by setting X9=1 (none of the nine points lies on X9=0)
  X9*T - 1
]>;
// eliminate all variables except a and b, thus giving us the condition, in terms of (a,b), for when the divisor D is reducible
Basis(EliminationIdeal(I,10));
