/* Here we verify that there are at most nine pairwise distinct ways of gluing E1 and E2 along the 3-torsion if j(E1)=j(E2). Suppose
   E1: x^3 + y^3 + z^3 + 3*a*x*y*z = 0
   E2: x^3 + y^3 + z^3 + 3*b*x*y*z = 0  */

// the invariants of C whose Jacobian (3,3) splits as E1 x E2 are as follows
function InvariantsOfC(a,b)
	return [
	72*(-20 + 16*a^3 + 40*a^6 + 112*a*b + 100*a^4*b - 32*a^7*b -
	68*a^2*b^2 - 104*a^5*b^2 + a^8*b^2 + 16*b^3 + 44*a^3*b^3 +
	54*a^6*b^3 + 100*a*b^4 + 65*a^4*b^4 - 30*a^7*b^4 -
	104*a^2*b^5 - 88*a^5*b^5 + 40*b^6 + 54*a^3*b^6 + 9*a^6*b^6 -
	32*a*b^7 - 30*a^4*b^7 + a^2*b^8),
	36*(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)^4*
	(320 + 160*a^3 + 256*a*b + 8*a^4*b + 240*a^2*b^2 + 160*b^3 +
	240*a^3*b^3 + 8*a*b^4 + 9*a^4*b^4),
	72*(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)^4*
	(-55040 + 74624*a^3 + 219552*a^6 + 84224*a^9 - 8*a^12 +
	314112*a*b + 564480*a^4*b + 181152*a^7*b - 50160*a^10*b +
	88512*a^2*b^2 - 93600*a^5*b^2 - 167112*a^8*b^2 +
	480*a^11*b^2 + 74624*b^3 + 383424*a^3*b^3 + 455568*a^6*b^3 +
	156928*a^9*b^3 + 60*a^12*b^3 + 564480*a*b^4 + 761040*a^4*b^4 +
	81072*a^7*b^4 - 121608*a^10*b^4 - 93600*a^2*b^5 -
	462096*a^5*b^5 - 358740*a^8*b^5 - 2160*a^11*b^5 + 219552*b^6 +
	455568*a^3*b^6 + 336444*a^6*b^6 + 106560*a^9*b^6 +
	81*a^12*b^6 + 181152*a*b^7 + 81072*a^4*b^7 - 148932*a^7*b^7 -
	70794*a^10*b^7 - 167112*a^2*b^8 - 358740*a^5*b^8 -
	201555*a^8*b^8 - 3402*a^11*b^8 + 84224*b^9 + 156928*a^3*b^9 +
	106560*a^6*b^9 + 30456*a^9*b^9 - 50160*a*b^10 -
	121608*a^4*b^10 - 70794*a^7*b^10 + 729*a^10*b^10 +
	480*a^2*b^11 - 2160*a^5*b^11 - 3402*a^8*b^11 - 8*b^12 +
	60*a^3*b^12 + 81*a^6*b^12),
	36864*(1 + a^3)*(1 + b^3)*(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)^12
];
end function;

R<x>:=PolynomialRing(QQ);
F<w>:=ext<QQ|x^2+x+1>;
K<a>:=FunctionField(F);
WP:=WeightedProjectiveSpace(K,[1,2,3,5]);

// elements of the Hesse pencil that are isomorphic to E1 are defined by these 12 parameters (and there are no other twists of E1 in the pencil)
allParams:=func<a|[a,a*w,a*w^2,(2 - a)/(1 + a),(2 - a)/(1 + a)*w,(2 - a)/(1 + a)*w^2,(2 - a*w^2)/(1 + a*w^2),(2 - a*w^2)/(1 + a*w^2)*w,(2 - a*w^2)/(1 + a*w^2)*w^2,(2 - a*w)/(1 + a*w),(2 - a*w)/(1 + a*w)*w,(2 - a*w)/(1 + a*w)*w^2]>;

/* Gluing E1 with these 12 curves gives all possibile isomorphism classes of Jac(C) as a ppav (or, equivalently, isomorphism classes of C) 
   that can be obtained by gluing two twists of E1. Of the 12 curves C so obtained, some are isomorphic, leaving 9 unique curves, up to isomorphism
   in general. (There are fewer than 9 if #Aut(E1)>2 or if E1 has an endomorphism of degree 2.) */

// We verify that some invariants match:
WP!InvariantsOfC(a,(2 - a*w^2)/(1 + a*w^2)*w) eq WP!InvariantsOfC(a, (2 - a*w)/(1 + a*w)*w^2);
WP!InvariantsOfC(a,(2 - a)/(1 + a)*w) eq WP!InvariantsOfC(a,(2 - a*w)/(1 + a*w));
WP!InvariantsOfC(a,(2 - a)/(1 + a)*w^2) eq WP!InvariantsOfC(a,(2 - a*w^2)/(1 + a*w^2));

// The remaining 9 classes are unique (for almost all a)
L:=[WP!InvariantsOfC(a,b) : b in [a, a*w, a*w^2, (2-a)/(1+a), (2 - a*w)/(1 + a*w)*w, (2 - a*w)^2/(1 + a*w^2)*w^2, (2 - a)/(1 + a)*w, (2 - a)/(1 + a)*w^2, (2 - a*w^2)/(1 + a*w^2)*w]];
&and[&and[L[i] ne L[j] : j in [i+1..9]] : i in [1..8]]; // no repetitions in the list


// Since we have a model for C, we can verify that those C corresponding to the cases with matching invariants are actually isomorphic.
A2<x,y>:=AffineSpace(K,2);
C:=func<a,b|Curve(A2, -3*(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)*y^2 + ((2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)^2*x^3
		 - 3*(2*a + a^4 + 3*b^2 - 2*a*b^3)*(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)*x^2
		 - 9*(-1 + a*b)*(a + b^2)*(a + 2*a^4 + 3*a^2*b + 3*b^2 - a*b^3)*x
		 - (-1 + 4*a^3 + 6*a*b + 3*a^2*b^2 + 4*b^3)*(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)
	  )*(
		(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)*(-1 + 4*a^3 + 6*a*b + 3*a^2*b^2 + 4*b^3)*x^3
		 - 9*(a^2 + b)*(-1 + a*b)*(-3*a^2 - b + a^3*b - 3*a*b^2 - 2*b^4)*x^2
	 	 - 3*(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)*(-3*a^2 - 2*b + 2*a^3*b - b^4)*x
	 	 - (2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)^2
	  ))>;

/* In the following cases, it is assumed that a^3+1 and 2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3 are non-zero (for the appropriate b that defines
   a curve isomorphic to the one defined by a). This is why the denominators in the coefficients do not vanish. */

// case 1:
C1:=C(a, (2 - a*w^2)/(1 + a*w^2)*w);
C2:=C(a,  (2- a*w)/(1 + a*w)*w^2);
v1:= -w^2*(a^6 - 3*a^5 - 3*a^4 + 11*a^3 + 60*a^2 + 15*a + 19) / (a^2 + 2*a - 2) / (a^4 - 5*a^3 - 8*a - 5);
v2:= 3*(w-1)*(a + w)^5*(a^2 - a - 3*w - 2)^3*(a^2 - a + 3*w + 1)^3*(a^2 + (-3*w - 1)*a + 1)^3 / (a + w^2)^5 / (a^2 + 2*a - 2)^3 / (a^4 - 5*a^3 - 8*a - 5)^3;
v3:= w^2*(4*a^6 - 3*a^5 + 15*a^4 - 19*a^3 + 6*a^2 + 6*a + 13) / (a^2 + 2*a - 2) / (a^4 - 5*a^3 - 8*a - 5);
iso:=map<C1->C2|[(x + v1)/(v3*x - w), v2*y/(v3*x - w)^3]>;

// case 2:
C1:=C(a, (2 - a)/(1 + a)*w);
C2:=C(a, (2 - a*w)/(1 + a*w));
v1 := ((w + 1)*a^6 + 3*a^5 + 3*w*a^4 + (11*w + 11)*a^3 - 60*a^2 - 15*w*a + 19*w + 19)/(a^6 - 3*w*a^5 + (12*w + 12)*a^4 + 2*a^3 - 21*w*a^2 + (-6*w - 6)*a + 10);
v2 := -3*(2+w)*(a + 1)^5*(a^2 + (-w - 3)*a - w - 1)^3*(a^2 - w*a - w + 2)^3*(a^2 - w*a + 2*w - 1)^3 / (a - w - 1)^5 / (a^2 + 2*w*a + 2*w + 2)^3 /(a^4 - 5*w*a^3 - 8*a - 5*w)^3;
v3 := (4*a^6 - 3*w*a^5 + (-15*w - 15)*a^4 - 19*a^3 + 6*w*a^2 + (-6*w - 6)*a + 13)/(a^6 - 3*w*a^5 + (12*w + 12)*a^4 + 2*a^3 - 21*w*a^2 + (-6*w - 6)*a + 10);
iso:=map<C1->C2|[(x + v1)/(v3*x - w^2), v2*y/(v3*x - w^2)^3]>;

// case 3 is just case 2 with w replaced by w^2
