## Background
A genus-two curve _C: y^2 = a*x^6 + b*x^4 + c*x^2 + d_ is a double cover of elliptic curves
_E: y^2 = a*x^3 + b*x^2 + c*x + d_
_E': y^2 = d*x^3 + c*x^2 + b*x + a_
via the obvious morphisms _(x,y) ↦ (x^2,y)_ and _(x,y) ↦ (1/x^2,y/x^3)._

### Verifying that _Jac(C)_ is _(2,2)_-isogenous to _E × E'._
The file _complementary_curve.m_ contains verification of the fact that _Jac(C)/E=E'_ over the ground field,
rather than just geometrically. Moreover, if _C_ has automorphism group larger than V<sub>4</sub> (i.e. D<sub>4</sub> or larger),
this corresponds to _a=d_ and _b=c,_ and therefore _E=E'_, so it covers _E_ in two different ways. However, in this case, _C_ also covers
the elliptic curve 
_Ê: y^2 = (a + b)/2*x^3 + (15*a - b)/2*x^2 + (15*a - b)/2*x + (a + b)/2_
via (x,y) ↦ ((x-1)^2/(x+1)^2, 4*y/(x+1)^3) and (x,y) ↦ ((x+1)^2/(x-1)^2, 4*y/(x-1)^3).
Contrary to some claims in the literature, _Ê_ is _not_ complementary to _E_ in _Jac(C)._
Rather, we have _Jac(C)/E=E_ and _Jac(C)/Ê=Ê._

Our approach here is based on the early chapters of Cassels and Flynn's _Prolegomena to a Middlebrow Arithmetic of Curves of Genus 2._
