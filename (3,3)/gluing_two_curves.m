// dehomogenize a homogeneous polynomial
function Dehomogenize(f)
  S := Parent(f);
  R := PolynomialRing(BaseRing(S));
  p1 := hom< S -> R | [ R.1, 1 ] >(f);
  p2 := hom< S -> R | [ 1, R.1 ] >(f);
  if Degree(p1) ge Degree(p2) then
    return p1;
  else
    return p2;
  end if;
end function;

S<y> := PolynomialRing(Rationals());
K<w> := NumberField(1+y+y^2);
R<x> := PolynomialRing(K);
P8<X1,X2,X3,X4,X5,X6,X7,X8,X9> := ProjectiveSpace(K,8);
P3<Y1,Y2,Y3,Y4> := ProjectiveSpace(K,3);
P2<X,Y,Z> := ProjectiveSpace(K,2);
P1<u,v> := ProjectiveSpace(K,1);
WP := WeightedProjectiveSpace(K,[1,2,3,5]);

// our formulas for the Igusa-Clebsch invariants (obtained by interpolation)
function ComputedInvariants(a,b)
return [72*(-20 + 16*a^3 + 40*a^6 + 112*a*b + 100*a^4*b - 32*a^7*b -68*a^2*b^2 - 104*a^5*b^2 + a^8*b^2 + 16*b^3 + 44*a^3*b^3 +54*a^6*b^3 + 100*a*b^4 + 65*a^4*b^4 - 30*a^7*b^4 -104*a^2*b^5 - 88*a^5*b^5 + 40*b^6 + 54*a^3*b^6 + 9*a^6*b^6 -32*a*b^7 - 30*a^4*b^7 + a^2*b^8),
  36*(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)^4*(320 + 160*a^3 + 256*a*b + 8*a^4*b + 240*a^2*b^2 + 160*b^3 +240*a^3*b^3 + 8*a*b^4 + 9*a^4*b^4),
  72*(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)^4*(-55040 + 74624*a^3 + 219552*a^6 + 84224*a^9 - 8*a^12 +314112*a*b + 564480*a^4*b + 181152*a^7*b - 50160*a^10*b +88512*a^2*b^2 - 93600*a^5*b^2 - 167112*a^8*b^2 +480*a^11*b^2 + 74624*b^3 + 383424*a^3*b^3 + 455568*a^6*b^3 +156928*a^9*b^3 + 60*a^12*b^3 + 564480*a*b^4 + 761040*a^4*b^4 +81072*a^7*b^4 - 121608*a^10*b^4 - 93600*a^2*b^5 -462096*a^5*b^5 - 358740*a^8*b^5 - 2160*a^11*b^5 + 219552*b^6 +455568*a^3*b^6 + 336444*a^6*b^6 + 106560*a^9*b^6 +81*a^12*b^6 + 181152*a*b^7 + 81072*a^4*b^7 - 148932*a^7*b^7 -70794*a^10*b^7 - 167112*a^2*b^8 - 358740*a^5*b^8 -201555*a^8*b^8 - 3402*a^11*b^8 + 84224*b^9 + 156928*a^3*b^9 +106560*a^6*b^9 + 30456*a^9*b^9 - 50160*a*b^10 -121608*a^4*b^10 - 70794*a^7*b^10 + 729*a^10*b^10 +480*a^2*b^11 - 2160*a^5*b^11 - 3402*a^8*b^11 - 8*b^12 +60*a^3*b^12 + 81*a^6*b^12),
  36864*(1 + a^3)*(1 + b^3)*(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)^12];
end function;

function VerifyInvariants(a,b)
  if a^3 + 1 eq 0 then
    print("Error: The curve defined by the first parameter is singular.");
    return false;
  elif b^3 + 1 eq 0 then
    print("Error: The curve defined by the second parameter is singular.");
    return false;
  elif 3*a^2*b^2 + a^3 + b^3 - 3*a*b + 2 eq 0 then
    print("Error: The 3-torsion isomorphism is induced by a 2-isogeny.");
    return false;
  end if;

  // parameters defining E1: x^3 + y^3 + z^3 + s x y z = 0 and E2: x^3 + y^3 + z^3 + t x y z = 0
  s := 3*a;
  t := 3*b;

  // A = E1 x E2, embedded in IP^8 via the Segre embedding
  A := Scheme(P8, [
    X3^3 + X6^3 + X9^3 + s*X3*X6*X9,
    X2^3 + X5^3 + X8^3 + s*X2*X5*X8,
    X1^3 + X4^3 + X7^3 + s*X1*X4*X7,
    X7^3 + X8^3 + X9^3 + t*X7*X8*X9,
    X4^3 + X5^3 + X6^3 + t*X4*X5*X6,
    X1^3 + X2^3 + X3^3 + t*X1*X2*X3,
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

  // The effective divisor on A that is linearly equivalent to 3Θ and fixed by [-1] and translation by A[3](K)
  D := Scheme(P8, [ X1 + X5 + X9 ]) meet A;

  // points of order 2 on E1 and E2
  A21 := Scheme(P8, [ 2*X5^3 + s*X5^2*X8 + X8^3, X1 + X5, X2 - X5, X3, X4 + X5, X6, X7 + X8, X9 ]);
  A22 := Scheme(P8, [ 2*X5^3 + t*X5^2*X6 + X6^3, X1 + X5, X2 + X5, X3 + X6, X4 - X5, X7, X8, X9 ]);

  // the composition A --> J=A/G --> J/[-1]
  psi := map< P8 -> P3 | [ X1^2 + X5^2 + X9^2, X2*X4 + X3*X7 + X6*X8, X2*X3 + X4*X6 + X7*X8, X2*X8 + X3*X6 + X4*X7 ]>;
  
  // psi(D) is a conic contained in Y1 + 2*Y2 = 0 (since X1+X5+X9=0 on D) so we project to IP^2 by dropping the first coordinate
  q := map< P8 -> P2 | [ X2*X4 + X3*X7 + X6*X8, X2*X3 + X4*X6 + X7*X8, X2*X8 + X3*X6 + X4*X7 ]>;

  // H is the conic that is the image of C in J/[-1], projected to IP^2
  H := q(D);

  // B is the branch locus of the canonical map C --> H
  B := q(Union(A21,A22));

  // we find the inverse of the parametrization IP^1 --> H
  paramStrings := Split(Sprint(Parametrization(Conic(Curve(H)))),"\n");
  coord1 := eval paramStrings[#paramStrings-1];
  coord2 := eval paramStrings[#paramStrings];
  paraminv := map< P2 -> P1 | [ coord1, coord2 ] >;

  // from the branch locus of the canonical map C --> IP^1, we recover C (up to quadratic twists)
  branch := paraminv(B);
  poly := Basis(Ideal(branch))[1];
  poly := Dehomogenize(poly);

  // we compare the actual Igusa-Clebsch invariants with our formula
  return WP!(IgusaClebschInvariants(HyperellipticCurve(poly))) eq  WP!(ComputedInvariants(a,b));
end function;
