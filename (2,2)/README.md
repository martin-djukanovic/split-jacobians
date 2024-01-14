## Background
A genus-two curve _C: y<sup>2</sup> = ax<sup>6</sup> + bx<sup>4</sup> + cx<sup>2</sup> + d_ is a double cover of elliptic curves

_E: y^2 = ax<sup>3</sup> + bx<sup>2</sup> + cx + d_

_E': y^2 = dx<sup>3</sup> + cx<sup>2</sup> + bx + a_

via the obvious morphisms _(x, y) ↦ (x<sup>2</sup>, y)_ and _(x, y) ↦ (1/x<sup>2</sup>, y/x<sup>3</sup>)._

### Verifying that _Jac(C)_ is _(2,2)_-isogenous to _E × E'._
The file _complementary_curve.m_ contains verification of the fact that _Jac(C)/E=E'_ over the ground field,
rather than just geometrically. Moreover, if _C_ has automorphism group larger than V<sub>4</sub> (i.e. D<sub>4</sub> or larger),
this corresponds to _a=d_ and _b=c,_ and therefore _E=E'_, so _C_ covers _E_ in two different ways. However, in this case, _C_ also covers the elliptic curve

_Ê: 2y<sup>2</sup>= (a + b)x<sup>3</sup> + (15a - b)x<sup>2</sup> + (15a - b)x + (a + b)_

via (x,y) ↦ ((x-1)<sup>2</sup>/(x+1)<sup>2</sup>, 4y/(x+1)<sup>3</sup>) and (x,y) ↦ ((x+1)<sup>2</sup>/(x-1)<sup>2</sup>, 4y/(x-1)<sup>3</sup>).

Contrary to some claims in the literature, _Ê_ is _not_ complementary to _E_ in _Jac(C)._ Rather, we have _Jac(C)/E=E_ and _Jac(C)/Ê=Ê._ Our approach here is based on the early chapters of Cassels and Flynn's _Prolegomena to a Middlebrow Arithmetic of Curves of Genus 2._


### Computing the (geometric) isomorphism classes of _E_ and _E'_ for a given _C._
The file _computing_components_of_Jac(C).m_ contains a function that given a hyperelliptic curve of genus 2 returns the j-invariants of _E_ and _E'_ if _Jac(C)_ is _(2,2)_-split.
