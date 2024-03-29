/*  Here we describe a family of genus-2 curves that admit a model of the form y^2=P(x)Q(x), where
    P(x)=x^3 + a*x^2 + b*x + c and Q(x)=4*c*x^3 + b^2*x^2 + 2*b*c*x + c^2, and admit an involution
    (x,y) |--> (m(x), y*n(x)) such that m(x) sends one root of P(x) to a root of Q(x) and swaps the other two roots of P(x)
    (and sends one root of Q(x) to a root of P(x) and swaps the other two roots of Q(x)).
    In this case, Jac(C) is (3,3)-split as E1 x E2, where E1 and E2 are elliptic curves that are 8-isogenous.
    
    The family is parametrized by a genus-0 curve X8 that we determined previously; a point [a:b:c] in P(1,2,3) determines
    the coefficients of P(x) and Q(x), and the curve C up to isomorphism.
*/

PP<a,b,c>:=WeightedProjectiveSpace(QQ,[1,2,3]);
X8:=Scheme(PP, -16*a^4*b^10 + 81*a^2*b^11 - 324*b^12 + 32*a^5*b^8*c + 54*a^3*b^9*c + 2250*a*b^10*c + 320*a^4*b^7*c^2 - 16535*a^2*b^8*c^2 + 16929*b^9*c^2 - 1280*a^5*b^5*c^3 + 24624*a^3*b^6*c^3 - 69300*a*b^7*c^3 - 10864*a^4*b^4*c^4 + 443087*a^2*b^5*c^4 - 333187*b^6*c^4 + 11168*a^5*b^2*c^5 - 781106*a^3*b^3*c^5 + 274410*a*b^4*c^5 + 128*a^6*c^6 + 374040*a^4*b*c^6 - 1503225*a^2*b^2*c^6 + 3459375*b^3*c^6 + 2092500*a^3*c^7 - 1215000*a*b*c^7 - 11390625*c^8);
A1<t>:=AffineSpace(QQ,1);

// a parametrization of X8
p:=map<A1->X8| [3*t^4 + 6*t^3 - 16*t^2 + 18*t + 5, (t - 1)*(t + 1)^5*(3*t^2 - 11), (t - 1)^2*(t + 1)^8*(t^2 + 7)] >;

// the point defined by the parameter t defines the following family up to isomorphism
K<t>:=FunctionField(QQ);
A2<x,y>:=AffineSpace(K,2);
R<X>:=PolynomialRing(K);
h:=hom<Parent(x)->R|[X,0]>;
C:=Curve(A2,  -y^2 + ((t - 1)*x + t + 1)*((t + 1)^3*x^2 + 2*(t^3 + 2*t^2 - 9*t - 2)*x + (t + 1)*(t^2 + 7)) * (t^2 + 7 + 4*(t^2 - 1)*x)*((t^2 + 7)*x^2 + 2*(t^2 - 9)*x + t^2 + 7));
E1:=Curve(A2, -y^2 + x^3 + 4*(3*t - 1)*(7*t^4 + 8*t^3 - 22*t^2 + 104*t + 31)*x^2 + 4*(t + 3)*(3*t - 1)^2*(3*t + 1)*(27*t^6 + 54*t^5 + 117*t^4 + 852*t^3 - 1339*t^2 + 1270*t + 299)*x + 256*(t + 3)^2*(3*t - 1)^6*(3*t + 1)^2*(t^2 + 7));
E2:=Curve(A2, -y^2 + x^3 - (3*t - 1)*(21*t^4 + 78*t^3 + 272*t^2 - 126*t - 373)*x^2 + (t^2 - 1)*(3*t - 1)^2*(363*t^6 + 1380*t^5 + 4183*t^4 + 10912*t^3 + 15849*t^2 - 31364*t - 46379)*x - (t - 5)^3*(t - 1)^2*(t + 1)^2*(3*t - 1)^3*(7*t + 13)^3*(t^2 + 7));

// the additional involution on C
inv:=map<C->C | [
	-(t^2 + 7)*((t - 3)*(t + 1)*x + t^2 + 7)/((t - 3)*(t + 1)*(t^2 + 7) + (t - 1)*(t + 5)*(t^2 - 8*t - 1)*x),
	 8*(t^2 + 7)^3*(3*t - 1)^3*y/((t - 1)*(t + 5)*(t^2 - 8*t - 1)*x + (t - 3)*(t + 1)*(t^2 + 7))^3
]>;

// the degree-3 maps to elliptic curves E1 and E2
f1:=map<C->E1 | [
	-16*(3*t + 1)*(t + 3)*(3*t - 1)^4*x^2/(((t - 1)*x + t + 1)*((t + 1)*(t^2 + 7) + 2*(t^3 + 2*t^2 - 9*t - 2)*x + (t + 1)^3*x^2)),
	8*(3*t - 1)^3*(3*t + 1)*(t + 3)*(t + 1)^3*(x - 2)*((t^2 - 1)*x^2 + 2*(t^2 - 1)*x + t^2 + 7)*y/(((t - 1)*x + t + 1)^2*((t + 1)^3*x^2 + 2*(t^3 + 2*t^2 - 9*t - 2)*x + (t^2 + 7)*(t + 1))^2)
]>;
f2:=map<C->E2 | [
	(t^2 - 1)*(((3*t^2 - 11)*x + 3*(t^2 + 7))^2*((t^4 + 12*t^3 - 30*t^2 - 76*t + 29)*x + (t^2 + 7)*(t^2 + 5*t - 2)))/((4*(t^2 - 1)*x + t^2 + 7)*((t^2 + 7)*x^2 + 2*(t^2 - 9)*x +  t^2 + 7)), 
	(t^2 - 1)*(3*t + 1)^3*(((t - 3)*(t^2 + 8*t - 1)*x + (t + 1)*(t^2 + 7))*((t^5 - 3*t^4 + 126*t^3 + 134*t^2 - 191*t + 61)*x^2 + 2*(t - 1)*(t^2 + 7)^2*x + (t + 1)*(t^2 + 7)^2)*y)/((7 + t^2 - 4*x + 4*t^2*x)^2*(7 + t^2 - 18*x + 2*t^2*x + 7*x^2 + t^2*x^2)^2)
]>;

// the 8-isogeny E1 --> E2
isog8:=map<E1->E2|[
  ((3*t + 1)^2*x^8 + 16*(3*t - 1)*(t^2 + 7)*(67*t^4 + 210*t^3 + 48*t^2 - 130*t - 67)*x^7 +  16*(3*t - 1)^2*(3*t + 1)*(629*t^9 + 2743*t^8 + 11724*t^7 + 47492*t^6 + 75614*t^5 + 174506*t^4 + 402956*t^3 + 3396*t^2 - 404907*t - 199465)*x^6 -  64*(t + 3)*(3*t - 1)^3*(3*t + 1)^2*(419*t^11 + 7351*t^10 + 5689*t^9 - 10635*t^8 + 13246*t^7 - 575482*t^6 - 737518*t^5 - 359926*t^4 - 4778609*t^3 -    1787277*t^2 + 4808645*t + 2955345)*x^5 - 32*(t + 3)*(3*t - 1)^4*(3*t + 1)^3*(16959*t^14 + 186958*t^13 + 369189*t^12 + 383660*t^11 + 2943799*t^10 -    886382*t^9 - 1636699*t^8 + 22184168*t^7 - 121844795*t^6 - 113054062*t^5 + 47052119*t^4 - 872261972*t^3 - 450272571*t^2 + 871697230*t + 578422239)*x^4 -  256*(t + 3)^2*(3*t - 1)^5*(3*t + 1)^4*(3771*t^16 + 72444*t^15 + 175712*t^14 + 1314804*t^13 + 6010948*t^12 + 5173788*t^11 + 14523168*t^10 + 6286260*t^9 -    86342622*t^8 + 130837652*t^7 - 136893728*t^6 - 480372484*t^5 + 936780036*t^4 - 1350827436*t^3 - 1920034528*t^2 + 1437953884*t + 1405978203)*x^3 +  256*(t + 3)^2*(3*t - 1)^6*(3*t + 1)^5*(50949*t^19 + 392013*t^18 + 2216727*t^17 + 6500103*t^16 + 2201828*t^15 - 18206332*t^14 - 194254052*t^13 -    784757028*t^12 - 1085049562*t^11 - 1715531370*t^10 - 39601230*t^9 + 6894377042*t^8 - 3134210636*t^7 + 5695357396*t^6 + 16374327468*t^5 -    46457975188*t^4 + 37253772349*t^3 + 78031184581*t^2 - 41428380049*t - 48932652961)*x^2 + 1024*(t + 3)^3*(3*t - 1)^7*(3*t + 1)^6*  (48843*t^21 + 397305*t^20 + 2102922*t^19 + 8520606*t^18 + 25654887*t^17 + 77305149*t^16 + 122009848*t^15 + 69462760*t^14 - 166689754*t^13 -    2345403166*t^12 - 4224566148*t^11 - 5553408140*t^10 - 7182790954*t^9 + 20886014738*t^8 + 7219122168*t^7 - 4198795288*t^6 + 59322599247*t^5 -    99778498203*t^4 - 13167411702*t^3 + 152201015326*t^2 - 24635992445*t - 78412262543)*x + 256*(t + 3)^4*(3*t - 1)^8*(3*t + 1)^7*  (177147*t^23 + 1358127*t^22 + 6869367*t^21 + 33151275*t^20 + 118556541*t^19 + 430561737*t^18 + 1120335273*t^17 + 2812550229*t^16 + 6008794830*t^15 +    4440617302*t^14 + 5520239174*t^13 - 32042367154*t^12 - 96977502502*t^11 - 90411603086*t^10 - 235670047598*t^9 + 254685638250*t^8 + 408379745031*t^7 -    266580511989*t^6 + 1104963382547*t^5 - 1021611051753*t^4 - 1123662524455*t^3 + 1730847172917*t^2 + 205606752501*t - 856946551887)) / (64*(t + 1)^2*(x + 64*(3*t - 1)*(3*t + 1))*(x + 2*(t + 3)*(3*t - 1)*(3*t + 1)*(3*t^2 - 2*t + 11))^2* (x^2 + 4*(t - 3)^2*(t + 3)*(3*t - 1)*(3*t + 1)*x + 4*(t + 3)*(3*t - 1)^2*(3*t + 1)^2*(9*t^5 + 15*t^4 + 34*t^3 + 38*t^2 - 267*t + 235))^2),
  ((3*t + 1)^3*(x - 2*(3*t - 1)*(3*t + 1)*(3*t^3 + 7*t^2 + 5*t - 31))*(x^2 + 4*(t + 3)*(3*t - 1)*(3*t + 1)*(5*t^2 + 2*t + 13)*x +   4*(t + 3)*(3*t - 1)^2*(3*t + 1)^2*(9*t^5 + 15*t^4 + 34*t^3 + 294*t^2 + 245*t + 491))*(x^8 + 16*(t - 3)^2*(t + 3)*(3*t - 1)*(3*t + 1)*x^7 +   16*(t + 3)*(3*t - 1)^2*(3*t + 1)*(109*t^6 + 26*t^5 + 323*t^4 + 972*t^3 - 4877*t^2 + 3482*t + 1757)*x^6 +   64*(t + 3)*(3*t - 1)^3*(3*t + 1)^2*(477*t^9 + 1443*t^8 + 1568*t^7 + 6680*t^6 - 3758*t^5 + 13126*t^4 + 44680*t^3 - 173152*t^2 + 86057*t + 51551)*x^5 +   32*(t + 3)*(3*t - 1)^4*(3*t + 1)^3*(8313*t^12 + 47996*t^11 + 125226*t^10 + 457212*t^9 + 1031999*t^8 + 1027256*t^7 + 1306988*t^6 - 3110120*t^5 +     224647*t^4 + 9220684*t^3 - 27974902*t^2 + 11853932*t + 8074529)*x^4 + 256*(t + 3)^2*(3*t - 1)^5*(3*t + 1)^4*   (4293*t^14 + 20142*t^13 + 51975*t^12 + 292140*t^11 + 696381*t^10 + 1375762*t^9 + 4305303*t^8 + 3345512*t^7 + 5262791*t^6 - 8743310*t^5 - 24328915*t^4 +     43652012*t^3 - 61870793*t^2 + 19695502*t + 18076213)*x^3 + 256*(t + 3)^3*(3*t - 1)^6*(3*t + 1)^5*(8829*t^16 + 31536*t^15 + 124416*t^14 + 963264*t^13 +     2071156*t^12 + 5507536*t^11 + 17733232*t^10 + 12699296*t^9 + 64616278*t^8 + 45837520*t^7 + 63286240*t^6 + 21240704*t^5 - 661414012*t^4 +     672966704*t^3 - 637209808*t^2 + 183947552*t + 214929589)*x^2 + 1024*(t + 3)^4*(3*t - 1)^7*(3*t + 1)^6*   (2187*t^18 - 1458*t^17 - 3645*t^16 + 125712*t^15 + 98604*t^14 + 2088936*t^13 + 9605628*t^12 + 9716016*t^11 + 58853738*t^10 + 15238388*t^9 +     103716970*t^8 + 101948912*t^7 - 39248068*t^6 + 507229480*t^5 - 1747655060*t^4 + 1240589008*t^3 - 911968861*t^2 + 272645806*t + 381212011)*x +   256*(t + 3)^4*(3*t - 1)^8*(3*t + 1)^7*(19683*t^21 + 137781*t^20 + 669222*t^19 + 2392578*t^18 + 4370355*t^17 + 5124141*t^16 + 12009384*t^15 -     3380616*t^14 + 169121574*t^13 + 739649194*t^12 + 1223389956*t^11 + 3814380844*t^10 + 1817087454*t^9 + 4252728066*t^8 + 2234747240*t^7 -     1188253384*t^6 + 15172248983*t^5 - 66353263039*t^4 + 34337911750*t^3 - 24519389406*t^2 + 13781455567*t + 14563951537))*y) / (512*(t + 1)^3*(x + 64*(3*t - 1)*(3*t + 1))^2*(x + 2*(t + 3)*(3*t - 1)*(3*t + 1)*(3*t^2 - 2*t + 11))^3* (x^2 + 4*(t - 3)^2*(t + 3)*(3*t - 1)*(3*t + 1)*x + 4*(t + 3)*(3*t - 1)^2*(3*t + 1)^2*(9*t^5 + 15*t^4 + 34*t^3 + 38*t^2 - 267*t + 235))^3)
]>;

// elliptic curves F1 and F2 which C also covers, 2-to-1
F1:=Curve(A2, -2*(3*t - 1)*(t^2 + 7)*y^2 + 2*(t - 1)*(t + 3)^2*(3*t + 1)*x^3 - (t^4 - 54*t^3 - 76*t^2 - 42*t + 43)*x^2 - 4*(t^4 - 3*t^3 - 13*t^2 - 9*t - 8)*x - (t - 1)^2*(t + 1)*(t + 3));
F2:=Curve(A2, -2*(3*t - 1)*(t^2 + 7)*y^2 + (t - 1)^2*(t + 1)*(t + 3)*x^3 - 4*(t^4 - 3*t^3 - 13*t^2 - 9*t - 8)*x^2 + (t^4 - 54*t^3 - 76*t^2 - 42*t + 43)*x + 2*(t - 1)*(3*t + 1)*(t + 3)^2);
H1:=map<F1->A2|[(3*t + 1)/((t - 1)*(3*t - 1)*(t^2 + 7))*x, (3*t + 1)/((t - 1)^2*(3*t - 1)*(t^2 + 7)*(t + 3))*y]>(F1);
H2:=map<F2->A2|[(t^2 + 4*t + 3)/(6*t^3 - 2*t^2 + 42*t - 14)*x, 1/(t-1)*(t^2 + 4*t + 3)/(6*t^3 - 2*t^2 + 42*t - 14)*y]>(F2);

H1:=EllipticCurve(h(Equation(H1)));
H2:=EllipticCurve(h(Equation(H2)));
K2,k2:=IsogenyFromKernel(H1, 2*(3*t - 1)*(t^2 + 7)*(t - 1)^2*X + (t + 1)*(3*t + 1));
IsIsomorphic(K2,H2);


// a simpler model of C on which the additional involutions are of the form (x,y)->(-x,y) and (x,y)->(-x,-y) and degree-2 maps to F1 and F2
C2:=map<C->A2|[((t^2 - 8*t - 1)*x + t^2 + 7)/((t - 1)*(t + 5)*x + t^2 + 7), 4*(t^2+7)/(t-1)*y/((t - 1)*(t + 5)*x + t^2 + 7)^3]>(C);
g1:=map<C2->F1|[ 1/x^2, (t-1) * y/x^3 ]>(C2);
g2:=map<C2->F2|[ -x^2,  (t-1) * y ]>(C2);


// a 2-isogeny E1-->F1, with kernel polynomial x + 64*(9*t^2 - 1)
isog1:=map<E1->F1|[
   ((t^2 + 7)*x^2 + 4*(t + 3)*(3*t - 1)*(t^4 - 14*t^3 + 8*t^2 - 34*t + 71)*(3*t + 1)*x + 4*(t + 3)^2*(3*t - 1)^2*(9*t^6 - 12*t^5 + 133*t^4 - 256*t^3 + 227*t^2 - 692*t + 719)*(3*t + 1)^2)/(16*(t - 1)*(t + 1)^2*(t + 3)^2*(3*t - 1)*(3*t + 1)*(x + 64*(9*t^2 - 1))),
   y*((t^2 + 7)*(2*(t + 3)*(3*t - 1)*(3*t + 1)*(3*t^2 - 2*t + 11) + x)*(2*(3*t - 1)*(3*t + 1)*(3*t^3 + 7*t^2 + 5*t - 31) - x))/(64*(t - 1)*(t + 1)^3*(t + 3)^2*(3*t - 1)^2*(3*t + 1)*(x + 64*(9*t^2 - 1))^2)
]>;

// a 2-isogeny E2-->F2, with kernel polynomial x - (t - 5)^3*(t + 1)*(3*t - 1)
isog2:=map<E2->F2|[
   ((t^2 + 7)*x^2 + 4*(t - 1)*(t + 1)*(4*t^4 - 17*t^3 - 137*t^2 - 123*t - 431)*(3*t - 1)*x + (t - 1)^2*(t + 1)^2*(307*t^6 + 2048*t^5 + 5099*t^4 + 20376*t^3 + 61369*t^2 + 60648*t + 106153)*(3*t - 1)^2)/(2*(t - 1)^2*(t + 1)*(t + 3)*(3*t - 1)*(3*t + 1)^2*(x - (t - 5)^3*(t + 1)*(3*t - 1))), 
   y*((t^2 + 7)*(x - (t - 1)*(t + 1)*(3*t - 1)*(19*t^2 + 34*t + 123))*((t + 1)*(3*t - 1)*(17*t^3 + 45*t^2 - 61*t + 127) + x))/(4*(t - 1)^2*(t + 1)*(t + 3)*(3*t - 1)^2*(3*t + 1)^3*((t - 5)^3*(t + 1)*(3*t - 1) - x)^2)
]>;

// a 2-isogeny F1-->F2, with kernel polynomial 2*(t - 1)*x + t + 1
isog3:=map<F1->F2|[
  ((t + 3)^2*(3*t + 1)*x^2 + 4*(t + 3)*(t^2 + t + 2)*x + 2*(t^3 + 3*t^2 + 5*t - 1))/((t + 1)*(t + 3)*(2*(t - 1)*x + t + 1)), 
  ((3*t + 1)*((t + 3)*x + 2)*((t - 1)*(t + 3)*x + t^2 + 2*t + 5)*y)/((t + 1)*(t + 3)*(2*(t - 1)*x + t + 1)^2)
]>;


// the j-invariants of the four elliptic curves
p1:=Equation(E1); p2:=Equation(E2);
p3:=Equation(F1); p4:=Equation(F2);
j1:=jInvariant(EllipticCurve(h(p1)));
j2:=jInvariant(EllipticCurve(h(p2)));
j3:=jInvariant(EllipticCurve(h(p3/Coefficient(p3,x,3))));
j4:=jInvariant(EllipticCurve(h(p4/Coefficient(p4,x,3))));

j1 eq 2*(47*t^4 + 660*t^3 + 970*t^2 - 780*t - 1153)^3/((t - 1)*(t + 1)*(t + 3)^2*(3*t + 1)^8);
j2 eq 2048*(t^4 - 10*t^2 + 1)^3/((t - 1)^2*(t + 1)^8*(t + 3)*(3*t + 1));
j3 eq 4*(73*t^4 + 60*t^3 - 10*t^2 + 60*t + 73)^3/((t - 1)^2*(t + 1)^2*(t + 3)^4*(3*t + 1)^4);
j4 eq 16*(13*t^4 + 60*t^3 + 110*t^2 + 60*t + 13)^3/((t - 1)^4*(t + 1)^4*(t + 3)^2*(3*t + 1)^2);



/************************************************************/
/* A simplified model of C, with the factor (3*t-1) removed */
/************************************************************/
K<t>:=FunctionField(QQ);
A2<x,y>:=AffineSpace(K,2);
// a (t - 1)*(3*t - 1)*(3*t + 1)*(t^2 + 7) twist of C
C0:=Curve(A2,  -(t - 1)*(3*t - 1)*(3*t + 1)*(t^2 + 7)*y^2 + ((t - 1)*x + t + 1)*((t + 1)^3*x^2 + 2*(t^3 + 2*t^2 - 9*t - 2)*x + (t + 1)*(t^2 + 7)) * (t^2 + 7 + 4*(t^2 - 1)*x)*((t^2 + 7)*x^2 + 2*(t^2 - 9)*x + t^2 + 7));

// a model of this twist on which the additional involution is given by (x,y)|-->(-x,y)
C:=Curve(A2, -y^2 + x^6 - 2*(3*t + 1)*(t^4 - 54*t^3 - 76*t^2 - 42*t + 43)*(t - 1)*x^4 - 32*(t + 3)^2*(3*t + 1)^3*(t^4 - 3*t^3 - 13*t^2 - 9*t - 8)*(t - 1)^3*x^2 - 32*(t + 1)*(t + 3)^5*(3*t + 1)^5*(t - 1)^7);

// an isomorphism C->C0
iso:=map<C->C0|[(t^2 + 7)*(6*t^3 + 14*t^2 - 14*t - x - 6)/((t^2 - 8*t - 1)*x - 2*(t - 1)^2*(t + 3)*(t + 5)*(3*t + 1)), 16*(t + 3)*(3*t - 1)^2*(t^2 + 7)*y/((t^2 - 8*t - 1)*x - 2*(t - 1)^2*(t + 3)*(t + 5)*(3*t + 1))^3]>;

// the model of C that appears on page 21 of the paper is obtained from the following model by replacing t by (1-2*t)/(1+2*t):
// (1 + 3*t)/(1 - t) gives a simpler model, but not simpler j-invariants for the four elliptic curves
CC := Curve(A2, -y^2 + x^6 - (t^4 - 54*t^3 - 76*t^2 - 42*t + 43)/(2*(t - 1)*(t + 3)^2*(3*t + 1))*x^4
	- 2*(t^4 - 3*t^3 - 13*t^2 - 9*t - 8)/((t - 1)*(t + 3)^2*(3*t + 1))*x^2
	- (t - 1)*(t + 1)/(2*(t + 3)*(3*t + 1)));
iso2:=map<C->CC|[1/(2*(3*t + 1)*(t - 1)*(t + 3))*x, 1/(2*(3*t + 1)*(t - 1)*(t + 3))^3*y]>;

// By composing with f1 and f2 above, we get the 3-to-1 maps from this twist to the corresponding twists of E1 and E2
E1:=Curve(A2, -(t - 1)*(3*t + 1)*(t^2 + 7)*y^2 + x^3 + 4*(7*t^4 + 8*t^3 - 22*t^2 + 104*t + 31)*x^2 + 4*(t + 3)*(3*t + 1)*(27*t^6 + 54*t^5 + 117*t^4 + 852*t^3 - 1339*t^2 + 1270*t + 299)*x + 256*(t + 3)^2*(3*t - 1)^3*(3*t + 1)^2*(t^2 + 7));
E2:=Curve(A2, -(t - 1)*(3*t + 1)*(t^2 + 7)*y^2 + x^3 - (21*t^4 + 78*t^3 + 272*t^2 - 126*t - 373)*x^2 + (t^2 - 1)*(363*t^6 + 1380*t^5 + 4183*t^4 + 10912*t^3 + 15849*t^2 - 31364*t - 46379)*x - (t - 5)^3*(t - 1)^2*(t + 1)^2*(7*t + 13)^3*(t^2 + 7));
f1:=map<C->E1|[
   (2*(t^2 + 7)*(x - 2*(t - 1)*(t + 3)*(3*t + 1))^2*((t^2 - 8*t - 1)*x - 2*(t + 3)*(t + 5)*(3*t + 1)*(t - 1)^2))/((x + 2*(3*t + 1)*(t - 1)^2)*(x^2 + 4*(t - 1)^2*(3*t + 1)*(t + 3)^3)), (16*(t + 1)^3*((t - 5)*x - 2*(t - 1)*(3*t + 1)*(t + 3)^2)*
   (x^2 + 4*(t + 3)*(t - 1)^2*x + 4*(t + 3)^2*(3*t + 1)*(t - 1)^3))*y/((x + 2*(3*t + 1)*(t - 1)^2)^2*(x^2 + 4*(t - 1)^2*(3*t + 1)*(t + 3)^3)^2)]>;
f2:=map<C->E2|[
   (2*(t + 1)*(t^2 + 7)*(x + (t - 1)*(t + 3)*(3*t + 1))^2*((5*t - 9)*x - 2*(t - 1)*(3*t + 1)*(t^2 - 14*t - 19)))/((x - 2*(-1 + t)^2*(1 + 3*t))*(x^2 + 2*(t - 1)*(t + 1)*(t + 3)^2*(3*t + 1)^2)), 
   (t + 1)*(3*t + 1)^3*(x + 4*(t + 3)*(3*t + 1))*(x^2 - 2*(t - 1)*(t + 3)*(3*t + 1)*x + 4*(t - 1)^2*(t + 1)*(t + 3)*(3*t + 1)^2)*y/((x - 2*(-1 + t)^2*(1 + 3*t))^2*(x^2 + 2*(t - 1)*(t + 1)*(t + 3)^2*(3*t + 1)^2)^2)
]>;

// the 2-to-1 maps to the corresponding twists
F1:=Curve(A2, -y^2 + x^3 - 2*(3*t + 1)*(t^4 - 54*t^3 - 76*t^2 - 42*t + 43)*(t - 1)*x^2 - 32*(t + 3)^2*(3*t + 1)^3*(t^4 - 3*t^3 - 13*t^2 - 9*t - 8)*(t - 1)^3*x - 32*(t + 1)*(t + 3)^5*(3*t + 1)^5*(t - 1)^7);
F2:=Curve(A2, -(3*t + 1)*(t - 1)*y^2 + x^3 - 8*(t^4 - 3*t^3 - 13*t^2 - 9*t - 8)*x^2 + 4*(t + 1)*(t + 3)*(t^4 - 54*t^3 - 76*t^2 - 42*t + 43)*(t - 1)^2*x + 16*(t + 1)^2*(t + 3)^4*(3*t + 1)*(t - 1)^5);
g1:=map<C->F1|[ x^2,  y ]>;
g2:=map<C->F2|[ -8*(t - 1)^4*(t + 1)*(t + 3)^3*(3*t + 1)^2/x^2, 4*(t - 1)^2*(t + 1)*(t + 3)^2*y/x^3 ]>;


R<X>:=PolynomialRing(K);
h:=hom<Parent(x)->R|[X,0]>;
E1:=EllipticCurve(h(Equation(E1)));
E2:=EllipticCurve(h(Equation(E2)));
F1:=EllipticCurve(h(Equation(F1)));
F2:=EllipticCurve(h(Equation(map<A2->A2|[x/((3*t + 1)*(t - 1)), y/((3*t + 1)*(t - 1))]>(F2))));

j1:= jInvariant(E1); j2:= jInvariant(E2); j3:= jInvariant(F1); j4:= jInvariant(F2); 
j1 eq 2*(47*t^4 + 660*t^3 + 970*t^2 - 780*t - 1153)^3/((t - 1)*(t + 1)*(t + 3)^2*(3*t + 1)^8);
j2 eq 2048*(t^4 - 10*t^2 + 1)^3/((t - 1)^2*(t + 1)^8*(t + 3)*(3*t + 1));
j3 eq 4*(73*t^4 + 60*t^3 - 10*t^2 + 60*t + 73)^3/((t - 1)^2*(t + 1)^2*(t + 3)^4*(3*t + 1)^4);
j4 eq 16*(13*t^4 + 60*t^3 + 110*t^2 + 60*t + 13)^3/((t - 1)^4*(t + 1)^4*(t + 3)^2*(3*t + 1)^2);

// these can be further simplified:
h:=hom<K->K|(1-2*t)/(1+2*t)>;
[h(j) : j in [j1,j2,j3,j4]];
