R<x>:=PolynomialRing(QQ);
F<w>:=ext<QQ|1+x+x^2>;
K<a,b>:=FunctionField(F,2);
P2<x,y,z>:=ProjectiveSpace(K,2);
E:=func<t|Curve(P2, x^3 + y^3 + z^3 + 3*t*x*y*z)>;

/* For a^3+1 non-zero, E(a) can be given the structure of an elliptic curve by choosing O=[-1:1:0] to be the identity element.
   The group morphisms are given by
   [-1]([x : y : z]) = [y : x : z]
   [2]([x : y : z]) = [y*(x^3 - z^3) : x*(z^3 - y^3) : z*(y^3 - x^3)]
   [x1 : y1 : z1] + [x2 : y2: z2] = [y1^2*x2*z2 - y2^2*x1*z1 : x1^2*y2*z2 - x2^2*y1*z1 : z1^2*x2*y2  - z2^2*x1*y1]
*/

// the following list of parameters defines isomorphic elliptic curves
L:=func<a|[
     a, a*w, a*w^2, (2 - a)/(1 + a), (2 - a)/(1 + a)*w, (2 - a)/(1 + a)*w^2,
     (2 - a*w)/(1 + a*w), (2 - a*w)/(1 + a*w)*w, (2 - a*w)/(1 + a*w)*w^2,
     (2 - a*w^2)/(1 + a*w^2), (2 - a*w^2)/(1 + a*w^2)*w, (2 - a*w^2)/(1 + a*w^2)*w^2
]>;
j:=func<a|-27*a^3*(a^3-8)^3/(a^3+1)^3>;
jInvariant(EllipticCurve(E(a),P2![-1,1,0])) eq j(a);
#Set([j(t): t in L(a)]) eq 1;

/* These two isomorphisms between elements of the pencil are enough to cover all 12 cases because all 12 parameters in L can be obtained
by composing a -> a*w and a -> (2 - a)/(1 + a).  */
f:=map<P2->P2 | [ w*x, w*y, z ]>;
g:=map<P2->P2 | [ w*x + w^2*y + z, w^2*x + w*y + z, x + y + z ]>;
f(E(a)) eq E(a*w) and g(E(a)) eq E((2 - a)/(1 + a));

// This yields the following:
f:=[map<P2->P2| I> : I in [
  [x, y, z],
  [w*x, w*y, z],
  [w^2*x, w^2*y, z],
  [w*x + w^2*y + z, w^2*x + w*y + z, x + y + z],
  [w^2*x + y + w*z, x + w^2*y + w*z, x + y + z],
  [x + w*y + w^2*z, w*x + y + w^2*z, x + y + z],
  [w^2*x + y + z, x + w^2*y + z, w*x + w*y + z],
  [x + w*y + w*z, w*x + y + w*z, w*x + w*y + z],
  [w*x + w^2*y + w^2*z, w^2*x + w*y + w^2*z, w*x + w*y + z],
  [x + w*y + z, w*x + y + z, w^2*x + w^2*y + z],
  [w*x + w^2*y + w*z, w^2*x + w*y + w*z, w^2*x + w^2*y + z],
  [w^2*x + y + w^2*z, x + w^2*y + w^2*z, w^2*x + w^2*y + z]
]];
&and[f[i](E(a)) eq E(L(a)[i]) : i in [1..12]];

/* Of course, each isomorphism can be composed with [-1]
   For us it is of interest how these isomorphisms affect 3-torsion, so we will provide a table for reference.
   The points S=[-1:0:1] and T=[-w:1:0] are generators of E(a)[3] for all curves in the pencil. We fix these to rigidify the setup
   and compute (E(a) x E(b))/G where G is the graph of S |--> S, T |--> -T.
   Isomorphisms E1[3] --> E2[3] that can be used to glue E1 and E2 are defined by sending (S,T) to:
   (T,S) or (-T,-S)
   (S+T,S) or (-S-T,-S)
   (-S+T,S) or (S-T,-S)
   (T,S+T) or (-T,-S-T)
   (T,S-T) or (-T,-S+T)
   (-S-T,T) or (S+T,-T)
   (S,-S-T) or (-S,S+T)
   (-S,-S+T) or (S,S-T)
   (S-T,-T) or (-S+T,T)
   (-S,T) or (S,-T)   <--- the one we use
   (S-T,S+T) or (-S+T,-S-T)
   (S+T,-S+T) or (-S-T,S-T)
   These 24 isomorphisms (or 12 after modding out [-1]) are precisely the ones inverting the Weil pairing.
   
   For example, if we want to glue E(a) and E(b) via (S,T) -> (T,S), we can instead apply an isomorphism to E(b) that sends (T,S) to (S,-T).
   This is accomplished by the isomorphism E(b) --> E((-b + 2)/(b + 1)), so gluing E(a) and E(b) along (S,T) -> (T,S) gives a p.p.a.s.
   that is isomorphic to the one obtained by gluing E(a) and E((-b + 2)/(b + 1)) along our chosen isomorphism (S,T) -> (S,-T).
*/

inv:=func<P|P2!([P[2],P[1],P[3]])>;
dbl:=func<P|P2!([P[2]*(P[1]^3 - P[3]^3), P[1]*(P[3]^3 - P[2]^3), P[3]*(P[2]^3 - P[1]^3)])>;
add:=func<P,Q|P2!([P[2]^2*Q[1]*Q[3] - Q[2]^2*P[1]*P[3], P[1]^2*Q[2]*Q[3] - Q[1]^2*P[2]*P[3], P[3]^2*Q[1]*Q[2]  - Q[3]^2*P[1]*P[2]])>;
S:=P2![-1,0,1];
T:=P2![-w,1,0];

/* We find which curve E(t) should be glued with E(a) along E(a)[3] --> E(t)[3] given by (S,T)-->(S,-T) to give a surface that is isomorphic
   to the one obtained by gluing E(a) --> E(b) along (S,T)-->(P,Q) */
function FindIso(P,Q)
  for i in [1..12] do
      if (f[i](P) eq S and f[i](Q) eq inv(T)) or (f[i](inv(P)) eq S and f[i](inv(Q)) eq inv(T)) then
        return <i, E(L(b)[i])>;
      end if;
  end for;
end function;

// (S,T) -> (T,S)   ~ E((2 - b)/(1 + b) 
FindIso(T,S);

// (S+T,S)          ~ E((2 - b)/(1 + b)*w^2)
FindIso(add(S,T),S);

// (T-S,T)          ~ E(b*w^2)
FindIso(add(inv(S),T),T);

// (T,S+T)          ~ E((2 - b*w)/(1 + b*w))
FindIso(T,add(S,T));

// (T,S-T)         ~ E((2 - b*w^2)/(1 + b*w^2))
FindIso(T,add(S,inv(T)));

// (S+T,-T)        ~ E(b*w)
FindIso(add(S,T),inv(T));

// (-S,S+T)       ~ E((2 - b*w)/(1 + b*w)*w)
FindIso(inv(S),add(S,T));

// (S,S-T)       ~ E((2 - b*w^2)/(1 + b*w^2)*w^2)
FindIso(S,add(S,inv(T)));

// (T-S,S)       ~ E((2 - b)/(1 + b)*w)
FindIso(add(T,inv(S)),S);

// (S-T,S+T)    ~ E((2 - b*w)/(1 + b*w)*w^2)
FindIso(add(S,inv(T)), add(S,T));

// (S+T,-S+T)   ~ E(2 - b*w^2)/(1 + b*w^2)*w)
FindIso(add(S,T), add(inv(S),T));





// Weierstrass model of x^3 + y^3 + z^3 + 3*t*x*y*z = 0
R<x>:=PolynomialRing(QQ);
K<w>:=ext<QQ|1+x+x^2>;
K<t>:=FunctionField(K);
P2<x,y,z>:=ProjectiveSpace(K,2);
a:=-3*t*(t^3 - 8);
b:=-2*(t^6 + 20*t^3 - 8);
E1:=Curve(P2, -y^2*z + x^3 + a*x*z^2 + b*z^3);
E2:=Curve(P2, x^3 + y^3 + z^3 + 3*t*x*y*z);
iso:=map<E1->E2|[3*t*x - (1 + 2*w)*y + 3*(t^3 + 4)*z,  3*t*x + (1 + 2*w)*y + 3*(t^3 + 4)*z, 6*(x - 3*t^2*z)]>;




/*  If K=K(w) with 1+w+w^2=0 and E/K is an elliptic curve such that E[3](K) has nine points 
    (i.e. E has fully K-rational 3-torsion) then E admits a Hessian model.  */
    
R<x>:=PolynomialRing(QQ);
K<w>:=ext<QQ|1+x+x^2>;
K<a,b>:=FunctionField(K,2);
P2<x,y,z>:=ProjectiveSpace(K,2);
F:=-y^2*z + x^3 + a*x*z^2 + b*z^3;
dd:=func<F,x,y|Derivative(Derivative(F,x),y)>;
M:=Matrix(CoordinateRing(P2), [
   [dd(F,x,x), dd(F,x,y), dd(F,x,z)],
   [dd(F,y,x), dd(F,y,y), dd(F,y,z)],
   [dd(F,z,x), dd(F,z,y), dd(F,z,z)]
]);
H:=1/8*Determinant(M);
S:=Scheme(P2,F) meet Scheme(P2,H);
IC:=IrreducibleComponents(S);
S:=IC[1]; if P2![0,1,0] in S then S:=IC[2]; end if;
Basis(EliminationIdeal(Ideal(S),{x,z}))[1] eq x^4 + 2*a*x^2*z^2 + 4*b*x*z^3 - 1/3*a^2*z^4;




/*  If #E[3](K)=9 then x^4 + 2*a*x^2 + 4*b*x- 1/3*a^2 splits completely over K, say as (x-t1)*(x-t2)*(x-t3)*(x-t4).
    Using Vieta's formulas we find the relations between the roots t1,t2,t3,t4.  */

R<x>:=PolynomialRing(QQ);
K<w>:=ext<QQ|1+x+x^2>;
R<T,a,b,t4,t1,t2,t3>:=PolynomialRing(K,7);
I:=ideal<R|[
   T*(4*a^3 + 27*b^2) - 1,
   t1 + t2 + t3 + t4,
   -2*a + t1*t2 + t1*t3 + t2*t3 + t1*t4 + t2*t4 + t3*t4, 
   4*b + t1*t2*t3 + t1*t2*t4 + t1*t3*t4 + t2*t3*t4,
   a^2 + 3*t1*t2*t3*t4
]>;



/* (t1,t2,t3) lies on the union of two quadric surfaces.  */
J:=EliminationIdeal(I,4);
J eq ideal<R| (t1^2  + w*t2^2 + w^2*t3^2 - 2*w^2*t1*t2 - 2*w*t1*t3 - 2*t2*t3)*(t1^2  + w^2*t2^2 + w*t3^2 - 2*w*t1*t2 - 2*w^2*t1*t3 - 2*t2*t3)>;



/* (t1,t2,t3) cannot satisfy both equations because the discriminant of E is non-zero.
   By renaming the roots, e.g. by swapping t2 and t3, we can ensure t1^2  + w*t2^2 + w^2*t3^2 - 2*w^2*t1*t2 - 2*w*t1*t3 - 2*t2*t3 = 0
   Now set t = ((1+2w)t1 + (1 + 3w)t2 - (1 + 3w^2)t3)/(t3 - t2)  and  d = 12/(t1 + t2*w + t3*w^2)
   and verify that ad^2 = -3t(t^3 - 8) and bd^3 = -2(t^6 + 20 t^3 - 8).
   This will establish that the d-twist of E is isomorphic to x^3 + y^3 + z^3 + 3*t*x*y*z = 0, with the isomorphism given on line 131.  */

R<x>:=PolynomialRing(QQ);
K<w>:=ext<QQ|1+x+x^2>;
R<T,t1,t2,t3,t4,a,b,t,d>:=PolynomialRing(K,9);
I:=ideal<R|[
   T*(4*a^3 + 27*b^2) - 1,
   t1 + t2 + t3 + t4,
   -2*a + t1*t2 + t1*t3 + t2*t3 + t1*t4 + t2*t4 + t3*t4, 
   4*b + t1*t2*t3 + t1*t2*t4 + t1*t3*t4 + t2*t3*t4,
   a^2 + 3*t1*t2*t3*t4,
   t1^2  + w*t2^2 + w^2*t3^2 - 2*w^2*t1*t2 - 2*w*t1*t3 - 2*t2*t3,
   -t*(t3 - t2) + (1+2*w)*t1 + (1 + 3*w)*t2 - (1 + 3*w^2)*t3,
   d*(t1 + t2*w + t3*w^2) + 12
]>;
a*d^2 + 3*t*(t^3 - 8) in I and  b*d^3 + 2*(t^6 + 20*t^3 - 8) in I;



/*  It remains to verify that d = u^2 in K. Suppose E[3] consists of [0:1:0] and [t1,±s1,1], [t2,±s2,1], [t3,±s3,1], [t4,±s4,1].
    Just as we picked a numbering for t1,t2,t3, we will have to pick signs for s1,s2,s3 here.  */

R<x>:=PolynomialRing(QQ);
K<w>:=ext<QQ|1+x+x^2>;
R<T,a,b,t1,t2,t3,t4,s1,s2,s3,s4>:=PolynomialRing(K,11);
f:=func<x|x^3+a*x+b>;
I:=ideal<R|[
   T*(4*a^3 + 27*b^2) - 1,
   t1 + t2 + t3 + t4,
   -2*a + t1*t2 + t1*t3 + t2*t3 + t1*t4 + t2*t4 + t3*t4, 
   4*b + t1*t2*t3 + t1*t2*t4 + t1*t3*t4 + t2*t3*t4,
   a^2 + 3*t1*t2*t3*t4,
   -s1^2 + f(t1),
   -s2^2 + f(t2),
   -s3^2 + f(t3),
   -s4^2 + f(t4),
   t1^2  + w*t2^2 + w^2*t3^2 - 2*w^2*t1*t2 - 2*w*t1*t3 - 2*t2*t3
]>;



/*  We find that the corresponding (s1,s2,s3) lies on exactly one of four quadric surfaces.  */
J:=EliminationIdeal(I,{s1,s2,s3});
J eq ideal<R| (s1*s2 + w*s1*s3 - w^2*s2*s3) * (s1*s2 + w*s1*s3 + w^2*s2*s3) * (s1*s2 - w*s1*s3 + w^2*s2*s3) * (s1*s2 - w*s1*s3 - w^2*s2*s3)>;



/*  By changing the signs of s1,s2,s3, we can ensure the first equation is satisfied, i.e. s1*s2 + w*s1*s3 = w^2*s2*s3.
    Now set u = (1 + 2*w)*(t3 - t2)/(w*s3 - w^2*s2) and verify that u^2 = d.  */

R<x>:=PolynomialRing(QQ);
K<w>:=ext<QQ|1+x+x^2>;
R<T,a,b,d,u,t1,t2,t3,t4,s1,s2,s3,s4>:=PolynomialRing(K,13);
f:=func<x|x^3+a*x+b>;
I:=ideal<R|[
   T*(4*a^3 + 27*b^2) - 1,
   t1 + t2 + t3 + t4,
   -2*a + t1*t2 + t1*t3 + t2*t3 + t1*t4 + t2*t4 + t3*t4, 
   4*b + t1*t2*t3 + t1*t2*t4 + t1*t3*t4 + t2*t3*t4,
   a^2 + 3*t1*t2*t3*t4,
   -s1^2 + f(t1),
   -s2^2 + f(t2),
   -s3^2 + f(t3),
   -s4^2 + f(t4),
   t1^2  + w*t2^2 + w^2*t3^2 - 2*w^2*t1*t2 - 2*w*t1*t3 - 2*t2*t3,
   s1*s2 + w*s1*s3 - w^2*s2*s3,
   d*(t1 + t2*w + t3*w^2) + 12,
   -u*(s1 + s3*w) + (1 + 2*w)*(t1 - t3)   //or -u*(s1 + w^2*s2) + (1 + 2*w)*(t1 - t2)  or  -u*(w*s3 - w^2*s2) + (1 + 2*w)*(t3 - t2)
]>;
d - u^2 in I;
