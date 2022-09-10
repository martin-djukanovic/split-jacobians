/* The base field is not of characteristic 2 or 3 and w denotes a primitive third root of unity.
   A plane model for C(a,b) that is obtained by gluing E1: x^3+y^3+z^3+3*a*x*y*z=0 and E2: x^3+y^3+z^3+3*b*x*y*z=0 along the 3-torsion by taking
   the quotient by the graph of the isomorphism E1[3]-->E2[3] given by [-1:0:1] |--> [-1:0:1] and [-w:1:0] |--> [-w^2:1:0] is obtained in 
   curve_C_in_P2_(derivation).m
      
   Here we give explicit isomorphisms
   C(a,b) -> C(a*w,b*w^2)
   C(a,b) -> C(a*w^2,b*w)
   C(a,b) -> C((2 - a)/(1 + a), (2 - b)/(1 + b))
   The first two are obvious, while the last one can be obtained by interpolation and verified.
*/

R<x>:=PolynomialRing(QQ);
F<w>:=ext<QQ|x^2+x+1>;
K<a,b>:=FunctionField(F,2);
A2<x,y>:=AffineSpace(K,2);
CC:=func<a,b|Curve(A2, -3*(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)*y^2 + ( 
		(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)^2*x^3
		 - 3*(2*a + a^4 + 3*b^2 - 2*a*b^3)*(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)*x^2
		 - 9*(-1 + a*b)*(a + b^2)*(a + 2*a^4 + 3*a^2*b + 3*b^2 - a*b^3)*x
		 - (-1 + 4*a^3 + 6*a*b + 3*a^2*b^2 + 4*b^3)*(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)
	  )*(
		(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)*(-1 + 4*a^3 + 6*a*b + 3*a^2*b^2 + 4*b^3)*x^3
		 - 9*(a^2 + b)*(-1 + a*b)*(-3*a^2 - b + a^3*b - 3*a*b^2 - 2*b^4)*x^2
	 	 - 3*(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)*(-3*a^2 - 2*b + 2*a^3*b - b^4)*x
	 	 - (2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)^2))>;
C:=CC(a,b);
C1:=CC(a*w,b*w^2);
C2:=CC(a*w^2,b*w);
C3:=CC((2 - a)/(1 + a), (2 - b)/(1 + b));

iso1:=map<C->C1|[x*w,y]>;
iso2:=map<C->C2|[x*w^2,y]>;
iso3:=map<C->C3|[-((2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3 + x - 3*a^2*x - a^3*x - 3*b*x - 3*a*b*x + 3*a^3*b*x + 3*a*b^2*x - b^3*x)/(1 - 3*a - a^3 - 3*a*b + 3*a^2*b - 3*b^2 - b^3 + 3*a*b^3 + 2*x + a^3*x - 3*a*b*x + 3*a^2*b^2*x + b^3*x)), 
  (1+2*w)*3^6*(a*b-1)^3*(a^2 - a*b + a + b^2 + b + 1)^3/((b + 1)^5*(a + 1)^5)*y/(1 - 3*a - a^3 - 3*a*b + 3*a^2*b - 3*b^2 - b^3 + 3*a*b^3 + 2*x + a^3*x - 3*a*b*x + 3*a^2*b^2*x + b^3*x)^3]>;
