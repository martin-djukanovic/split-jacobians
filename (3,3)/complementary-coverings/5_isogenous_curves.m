/*  Below is a 1-dimensional family of genus-2 curves C with the following properties:
    1) C admits complementary degree-3 maps f1:C-->E1 and f1:C-->E2, where E1 and E2 are elliptic curves
    2) C has an additional involution, that swaps the 3 Weierstrass points that are in the same fibre of f1 (or equivalently f2)
       with the remaining 3 Weierstrass points
   
    The elliptic curves E1 and E2 are then 5-isogenous and the 5-isogeny induces the coverings in the sense that
    Jac(C) = (E1 x E2)/G, where G is the graph of the isomorphism E1[3] --> E2[3] that is the restriction of the
    said isogeny to the 3-torsion.
    
    Therefore this is a 1-dimensional family of curves like those in Example 3.7.
*/

K<t>:=FunctionField(QQ);
A2<x,y>:=AffineSpace(K,2);
C:=Curve(A2, -y^2 + ((t^2 + 1)*x^3 - (t - 4)*(t^2 + 1)*x^2 + 2*(t + 2)*x + 2)*(2*(t^2 + 1)*x^3 + (t+2)^2*x^2 + 2*(t + 2)*x + 1));
E1:=Curve(A2, - y^2 + (t - 1)^6*(2*t - 11)*(t^2 + 1)*x^3 + 2*(t - 1)^3*(3*t - 14)*(t^2 + 1)*x^2 + (6*t^3 - 23*t^2 + 10*t - 20)*x + 2);
E2:=Curve(A2, - y^2 + (t^2 + 1)*x^3 - 2*(t - 1)*(t + 32)*(2*t - 11)*(t^2 + 1)*x^2 + (t - 1)^2*(2*t - 11)^2*(108*t^3 + 1233*t^2 + 386*t + 1204)*x - 2*(t - 1)^3*(2*t - 11)^3*(9*t + 13)^3);

// the additional involution
inv:=map<C->C | [-(t*x + 1)/((2*t - 1)*x + t), (t - 1)^3*y/((2*t - 1)*x + t)^3]>;

// the degree-3 maps
f1:=map<C->E1|[
  x^2/((t^2 + 1)*x^3 - (t - 4)*(t^2 + 1)*x^2 + 2*(t + 2)*x + 2),
  ((t^2 + 1)*x^3 - 2*(t + 2)*x - 4)*y/((t^2 + 1)*x^3 - (t - 4)*(t^2 + 1)*x^2 + 2*(t + 2)*x + 2)^2
]>;
f2:=map<C->E2|[
  (2*t - 11)*((t + 2)*x + 3)^2*((4*t^2 + 2*t - 7)*x + 3*t - 4)/(2*(t^2 + 1)*x^3 + (t+2)^2*x^2 + 2*(t + 2)*x + 1), 
  (2*t - 11)^3*((2*t^4 - 3*t^3 - 4*t^2 + 8*t - 4)*x^3 + (2*t^3 - 7*t^2 + 6*t - 4)*x^2 - (t + 2)*x - 1)*y/(2*(t^2 + 1)*x^3 + (t+2)^2*x^2 + 2*(t + 2)*x + 1)^2
]>;

// the 5-isogeny E2 --> E1
isog5:=map<E2->E1|[
(-4*(-1 + t)^5*(-11 + 2*t)^5*(5610344 + 6984872*t + 14471640*t^2 + 1215710*t^3 + 10235935*t^4 - 3644298*t^5 + 385641*t^6) + 
    (-1 + t)^4*(-11 + 2*t)^4*(6604288 + 1036720*t + 13784120*t^2 - 1713840*t^3 + 7593065*t^4 - 2396416*t^5 + 248400*t^6)*x - 4*(-1 + t)^3*(-11 + 2*t)^3*(1 + t^2)*(131512 - 15346*t + 127363*t^2 - 36684*t^3 + 3742*t^4)*
     x^2 + 2*(-1 + t)^2*(-11 + 2*t)^2*(1 + t^2)*(8438 - 1648*t + 8111*t^2 - 1984*t^3 + 200*t^4)*x^3 - 4*(-1 + t)*(-11 + 2*t)*(1 + t^2)^2*(56 - 10*t + t^2)*x^4 + (1 + t^2)^2*x^5)/
   ((-1 + t)^4*(-11 + 2*t)^3*((-1 + t)^2*(-11 + 2*t)^2*(504 + 44*t + 621*t^2) - 50*(-1 + t)*(-11 + 2*t)*(1 + t^2)*x + (1 + t^2)*x^2)^2), 
  ((-(-1 + t)^6)*(-11 + 2*t)^6*(-1084423552 + 1980853248*t - 3061281408*t^2 + 2893703760*t^3 - 2428404320*t^4 + 966558244*t^5 - 486414261*t^6 + 19525536*t^7) + 
    10*(-1 + t)^5*(-11 + 2*t)^5*(1 + t^2)*(-11027648 + 17917680*t - 24072520*t^2 + 11307640*t^3 - 9148615*t^4 + 279936*t^5)*x - 
    3*(-1 + t)^4*(-11 + 2*t)^4*(1 + t^2)*(-1901216 + 1955360*t - 4726740*t^2 + 1619080*t^3 - 2507805*t^4 + 50112*t^5)*x^2 + 4*(-1 + t)^3*(-11 + 2*t)^3*(1 + t^2)^2*(-60822 + 20812*t - 87409*t^2 + 896*t^3)*x^3 - 
    (-1 + t)^2*(-11 + 2*t)^2*(1 + t^2)^2*(-8044 + 484*t - 9683*t^2 + 32*t^3)*x^4 - 150*(-1 + t)*(-11 + 2*t)*(1 + t^2)^3*x^5 + (1 + t^2)^3*x^6)*
   (y/((-1 + t)^3*(-11 + 2*t)^4*((-1 + t)^2*(-11 + 2*t)^2*(504 + 44*t + 621*t^2) - 50*(-1 + t)*(-11 + 2*t)*(1 + t^2)*x + (1 + t^2)*x^2)^3))
]>;

// j(E1) = -64*(124*t^2 + 114*t + 1)^3/(t*(11*t - 2)^5)
// j(E2) = -64*(4*t^2 - 6*t + 1)^3/(t^5*(11*t - 2))
