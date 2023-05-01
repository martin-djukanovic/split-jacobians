QQ:=Rationals();
K<a,b,c>:=FunctionField(QQ,3);
PP<A,B,C>:=WeightedProjectiveSpace(QQ,[1,2,3]);
A2<x,y>:=AffineSpace(K,2);
A1<T>:=AffineSpace(K,1);
R:=CoordinateRing(A2);
Phi:=func<n,j1,j2|map<A2->A1|[R!ClassicalModularPolynomial(n)]>([j1,j2])[1]>;
J:=[];

// j-invariants of  E: y^2 = x^3 + a x^2 + bx + c and E' : y^2 = c x^3 + b x^2 + a x + 1, of which C : y^2 = x^6 + a x^4 + bx^2 + c is a double cover.
J[2]:=[
	-256*(a^2 - 3*b)^3/(-a^2*b^2 + 4*b^3 + 4*a^3*c - 18*a*b*c + 27*c^2),
	-256*(b^2 - 3*a*c)^3/(c^2*(-a^2*b^2 + 4*b^3 + 4*a^3*c - 18*a*b*c + 27*c^2))
];

// j-invariants of the two components of Jac(C), of which C : y^2 = (x^3 + a x^2 + b x + c)(4 c x^3 + b^2 x^2 + 2 b c x + c^2) is a triple cover.
J[3]:=[
	16*(a^2*b^4 + 12*b^5 - 126*a*b^3*c + 216*a^2*b*c^2 + 405*b^2*c^2 - 972*a*c^3)^3/((b^3 - 27*c^2)^3*(-a^2*b^2 + 4*b^3 + 4*a^3*c - 18*a*b*c + 27*c^2)^2),
	-256*(a^2 - 3*b)^3/(-a^2*b^2 + 4*b^3 + 4*a^3*c - 18*a*b*c + 27*c^2)
];
h:=hom<K->CoordinateRing(PP)|[A,B,C]>;

// This function returns the irreducible components of Phi_N(j1,j2) in the weighted projective space IP(1,2,3).
// For general n we should probably compute this over the n-th cyclotomic field because not every component is necessarily geometrically irreducible.
function comps(N,n)
  eqn:=h(Numerator(Phi(N,J[n][1],J[n][2])));
  SS:=Scheme(PP,eqn);
  S:=[Curve(ReducedSubscheme(s)) : s in IrreducibleComponents(SS)];
  return S;
end function;

// This function returns the genera of the components. If given a prime p, it returns the genera modulo p (which is faster to compute)
function genera(S,p)
  if IsPrime(p) then
    g:=[Genus(Curve(Reduction(s,p))) : s in S];
  else
    g:=[Genus(s) : s in S];
  end if;
  return g;
end function;

// example 3-isogenies and 2-torsion
S:=comps(3,2);
g:=genera(S,5);
S[1];
g[1];
IsSingular(S[1],S[1]![2,1,0]);

// a component of genus zero with a smooth rational point can be rationally parametrized
// Parametrization(S[1],S[1]![2,1,0]);

/* From the parametrization [a:b:c] = f(t) we obtain the family of curves C, whose Jacobian is (n,n)-split as E1 x E2 with E1 and E2
   are geometrically N-isogenous. To find the smallest field over which they are isogenous we can consider replacing C by a suitable twist,
   in case C has a large (geometric) automorphism group. If that strategy fails, we determine the "twisting factor" d(t) by which we
   must twist E2 to obtain a curve N-isogenous to E1 so that E1 and E2 are N-isogenous over the ground field if s^2=d(t). This equation defines
   a curve (not necessarily of genus zero) that parametrizes the curves C whose Jacobian is (n,n)-split as E1 x E2 with E1 and E2 N-isogenous
   over the ground field.
*/
