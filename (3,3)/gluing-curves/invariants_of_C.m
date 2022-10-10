/* w is a primitive third root of unity, i.e. 1 + w + w^2 = 0.
   The function VerifyInvariants(a,b) will verify that gluing elliptic curves E1: x^3 + y^3 + z^3 + 3 a x y z = 0 and 
   E2: x^3 + y^3 + z^3 + 3 b x y z = 0, whose identity element is O=[-1:1:0], along the 3-torsion via the isomorphism E1[3] --> E2[3]
   defined by  [-1:0:1] |--> [-1:0:1] and [-w:0:1] |--> [-w^2:0:1], results in the Jacobian of a genus-2 curve C whose Igusa-Clebsch invariants
   are given by ComputedInvariants(a,b), unless 3*a^2*b^2 + a^3 + b^3 - 3*a*b + 2 = 0, in which case the isomorphism E1[3] --> E2[3]
   is the resitriction of a 2-isogeny E1 --> E2.
   
   Given bounds on the degree of the invariants in terms of a and b (which can be obtained by computing them for large integral values
   of a and b), verifying the formula given by ComputedInvariants(a,b) is correct for sufficiently many cases proves their correctness.
*/

QQ:=Rationals();

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

// ambient spaces
R<x> := PolynomialRing(QQ);
K<w> := NumberField(1+x+x^2);
R<x> := PolynomialRing(K);
P8<X1,X2,X3,X4,X5,X6,X7,X8,X9> := ProjectiveSpace(K,8);
P2<X,Y,Z> := ProjectiveSpace(K,2);
P1<u,v> := ProjectiveSpace(K,1);
WP1 := WeightedProjectiveSpace(K,[1,2,3,5]);
WP2 := WeightedProjectiveSpace(K,[1,2,3,4,5]);

// our formulas for the modular invariants of C (obtained by interpolation)
function ComputedIgusaClebschInvariants(a,b)
return [
    72*(9*a^6*b^6 - 30*(a^7*b^4 + a^4*b^7) - 88*a^5*b^5 + a^8*b^2 + a^2*b^8 + 54*(a^6*b^3 + a^3*b^6) + 65*a^4*b^4 - 32*(a^7*b + a*b^7) - 104*(a^5*b^2 + a^2*b^5) + 40*(a^6 + b^6) + 44*a^3*b^3 + 100*(a^4*b + a*b^4) - 68*a^2*b^2 + 16*(a^3 + b^3) + 112*a*b - 20),
    36*(3*a^2*b^2 + a^3 + b^3 - 3*a*b + 2)^4*(9*a^4*b^4 + 240*a^3*b^3 + 8*(a^4*b + a*b^4) + 240*a^2*b^2 + 160*(a^3 + b^3) + 256*a*b + 320),
    72*(3*a^2*b^2 + a^3 + b^3 - 3*a*b + 2)^4* (729*a^10*b^10 - 3402*(a^11*b^8 + a^8*b^11) + 30456*a^9*b^9 + 81*(a^12*b^6 + a^6*b^12) - 70794*(a^10*b^7 + a^7*b^10) - 201555*a^8*b^8 - 2160*(a^11*b^5 + a^5*b^11) + 60*(a^12*b^3 + a^3*b^12) + 106560*(a^9*b^6 + a^6*b^9) - 148932*a^7*b^7 - 121608*(a^10*b^4 + a^4*b^10) + 480*(a^11*b^2 + a^2*b^11) - 358740*(a^8*b^5 + a^5*b^8) - 8*(a^12 + b^12) + 156928*(a^9*b^3 + a^3*b^9) + 336444*a^6*b^6 - 50160*(a^10*b + a*b^10) + 81072*(a^7*b^4 + a^4*b^7) - 462096*a^5*b^5 - 167112*(a^8*b^2 + a^2*b^8) + 84224*(a^9 + b^9) + 455568*(a^6*b^3 + a^3*b^6) + 761040*a^4*b^4 + 181152*(a^7*b + a*b^7) - 93600*(a^5*b^2 + a^2*b^5) + 219552*(a^6 + b^6) + 383424*a^3*b^3 + 564480*(a^4*b + a*b^4) + 88512*a^2*b^2 + 74624*(a^3 + b^3) + 314112*a*b - 55040),
    36864*(a^3 + 1)*(b^3 + 1)*(3*a^2*b^2 + a^3 + b^3 - 3*a*b + 2)^12
  ];
end function;

function ComputedIgusaInvariants(a,b)
   return [
      9*(9*a^6*b^6 - 30*(a^7*b^4 + a^4*b^7) + a^8*b^2 + a^2*b^8 - 88*a^5*b^5 + 54*(a^6*b^3 + a^3*b^6) - 32*(a^7*b + a*b^7) + 65*a^4*b^4 - 104*(a^5*b^2 + a^2*b^5) + 40*(a^6 + b^6) + 44*a^3*b^3 + 100*(a^4*b + a*b^4) - 68*a^2*b^2 + 16*a^3 + 16*b^3 + 112*a*b - 20),
      -3*(729*(a^13*b^10 + a^10*b^13) - 972*(a^14*b^8 + a^8*b^14) - 3969*(a^12*b^9 + a^9*b^12) + 81*(a^15*b^6 + a^6*b^15) + 6102*(a^13*b^7 + a^7*b^13) + 11529*(a^11*b^8 + a^8*b^11) - 1881*(a^14*b^5 + a^5*b^14) - 17067*(a^12*b^6 + a^6*b^12) + 114*(a^15*b^3 + a^3*b^15) + a^16*b + a*b^16 - 14219*(a^10*b^7 + a^7*b^10) + 7808*(a^13*b^4 + a^4*b^13) + 29166*(a^11*b^5 + a^5*b^11) - 984*(a^14*b^2 + a^2*b^14) + 14492*(a^9*b^6 + a^6*b^9) - 14243*(a^12*b^3 + a^3*b^12) + 20*(a^15 + b^15) - 15956*(a^10*b^4 + a^4*b^10) + 2680*(a^13*b + a*b^13) + 19800*(a^8*b^5 + a^5*b^8) + 19308*(a^11*b^2 + a^2*b^11) + 980*(a^9*b^3 + a^3*b^9) - 1600*(a^12 + b^12) + 1944*a^11*b^11 - 26790*(a^7*b^4 + a^4*b^7) - 9488*(a^10*b + a*b^10) - 6021*a^10*b^10 + 17235*(a^8*b^2 + a^2*b^8) + 5328*a^9*b^9 + 17226*(a^6*b^3 + a^3*b^6) - 640*(a^9 + b^9) + 21501*a^8*b^8 - 20080*(a^7*b + a*b^7) - 34896*a^7*b^7 - 10536*(a^5*b^2 + a^2*b^5) + 52761*a^6*b^6 + 3112*(a^6 + b^6) - 26424*a^5*b^5 - 6172*(a^4*b + a*b^4) - 6923*a^4*b^4 + 3404*a^3*b^3 + 2320*(a^3 + b^3) - 7284*a^2*b^2 + 1712*a*b + 190),
      59049*(a^20*b^14 + a^14*b^20) + 39366*(a^18*b^15 + a^15*b^18) - 39366*(a^21*b^12 + a^12*b^21) - 459270*(a^19*b^13 + a^13*b^19) + 6561*(a^22*b^10 + a^10*b^22) - 454896*(a^17*b^14 + a^14*b^17) + 459270*(a^20*b^11 + a^11*b^20) + 1664307*(a^18*b^12 + a^12*b^18) - 138510*(a^21*b^9 + a^9*b^21) + 2288574*(a^16*b^13 + a^13*b^16) - 2202066*(a^19*b^10 + a^10*b^19) + 12636*(a^22*b^7 + a^7*b^22) - 3534354*(a^17*b^11 + a^11*b^17) + 937818*(a^20*b^8 + a^8*b^20) - 162*(a^23*b^5 + a^5*b^23) - 5794524*(a^15*b^12 + a^12*b^15) + 5803110*(a^18*b^9 + a^9*b^18) - 148176*(a^21*b^6 + a^6*b^21) + 4691655*(a^16*b^10 + a^10*b^16) - 3341034*(a^19*b^7 + a^7*b^19) + 8109*(a^22*b^4 + a^4*b^22) + 8748840*(a^14*b^11 + a^11*b^14) - 9043632*(a^17*b^8 + a^8*b^17) + 673440*(a^20*b^5 + a^5*b^20) - 138*(a^23*b^2 + a^2*b^23) - 2794498*(a^15*b^9 + a^9*b^15) + 7005421*(a^18*b^6 + a^6*b^18) - 55576*(a^21*b^3 + a^3*b^21) + a^24 + b^24 - 6525930*(a^13*b^10 + a^10*b^13) + 7291170*(a^16*b^7 + a^7*b^16) - 1754034*(a^19*b^4 + a^4*b^19) + 1758*(a^22*b + a*b^22) - 2902320*(a^14*b^8 + a^8*b^14) - 8948592*(a^17*b^5 + a^5*b^17) + 146469*(a^20*b^2 + a^2*b^20) - 4897294*(a^12*b^9 + a^9*b^12) + 455070*(a^15*b^6 + a^6*b^15) + 2751412*(a^18*b^3 + a^3*b^18) - 4520*(a^21 + b^21) + 5040828*(a^13*b^7 + a^7*b^13) + 5765400*(a^16*b^4 + a^4*b^16) - 198300*(a^19*b + a*b^19) + 8348526*(a^11*b^8 + a^8*b^11) - 11707326*(a^14*b^5 + a^5*b^14) - 2756412*(a^17*b^2 + a^2*b^17) - 9687918*(a^12*b^6 + a^6*b^12) - 922404*(a^15*b^3 + a^3*b^15) + 58756*(a^18 + b^18) - 118098*a^17*b^17 - 16123014*(a^10*b^7 + a^7*b^10) + 11428560*(a^13*b^4 + a^4*b^13) + 1047258*(a^16*b + a*b^16) + 905418*a^16*b^16 + 675420*(a^11*b^5 + a^5*b^11) - 3956232*(a^14*b^2 + a^2*b^14) - 2981610*a^15*b^15 + 4124680*(a^9*b^6 + a^6*b^9) - 8043346*(a^12*b^3 + a^3*b^12) - 90920*(a^15 + b^15) + 5347377*a^14*b^14 + 1449480*(a^10*b^4 + a^4*b^10) + 3159408*(a^13*b + a*b^13) - 3045906*a^13*b^13 + 783360*(a^8*b^5 + a^5*b^8) + 1254504*(a^11*b^2 + a^2*b^11) - 7419323*a^12*b^12 - 2197640*(a^9*b^3 + a^3*b^9) - 627440*(a^12 + b^12) + 19173930*a^11*b^11 - 1168542*(a^7*b^4 + a^4*b^7) + 2215680*(a^10*b + a*b^10) - 26821770*a^10*b^10 + 2430549*(a^8*b^2 + a^2*b^8) + 8067464*a^9*b^9 + 2317278*(a^6*b^3 + a^3*b^6) - 786176*(a^9 + b^9) + 357678*a^8*b^8 + 108288*(a^7*b + a*b^7) - 12141936*a^7*b^7 - 151464*(a^5*b^2 + a^2*b^5) + 9939345*a^6*b^6 - 373400*(a^6 + b^6) - 2171160*a^5*b^5 - 220380*(a^4*b + a*b^4) + 1073241*a^4*b^4 + 139052*a^3*b^3 - 59888*(a^3 + b^3) - 274020*a^2*b^2 - 25104*a*b + 580,
      -81*(a^3 + 1)*(b^3 + 1)*(-19683*(a^21*b^18 + a^18*b^21) + 19683*(a^24*b^15 + a^15*b^24) - 6561*(a^25*b^13 + a^13*b^25) + 395847*(a^20*b^17 + a^17*b^20) - 207765*(a^23*b^14 + a^14*b^23) + 2187*(a^26*b^11 + a^11*b^26) + 22599*(a^21*b^15 + a^15*b^21) + 114453*(a^24*b^12 + a^12*b^24) - 2817828*(a^19*b^16 + a^16*b^19) + 1034694*(a^22*b^13 + a^13*b^22) - 35964*(a^25*b^10 + a^10*b^25) + 101574*(a^20*b^14 + a^14*b^20) - 775413*(a^23*b^11 + a^11*b^23) + 3483*(a^26*b^8 + a^8*b^26) + 12577788*(a^18*b^15 + a^15*b^18) - 3155760*(a^21*b^12 + a^12*b^21) + 273753*(a^24*b^9 + a^9*b^24) - 27*(a^27*b^6 + a^6*b^27) - 989883*(a^19*b^13 + a^13*b^19) + 2826423*(a^22*b^10 + a^10*b^22) - 39564*(a^25*b^7 + a^7*b^25) + 9*(a^28*b^4 + a^4*b^28) - 34004241*(a^17*b^14 + a^14*b^17) + 6219855*(a^20*b^11 + a^11*b^20) - 1283679*(a^23*b^8 + a^8*b^23) + 1818*(a^26*b^5 + a^5*b^26) + 6258405*(a^18*b^12 + a^12*b^18) - 6861459*(a^21*b^9 + a^9*b^21) + 190272*(a^24*b^6 + a^6*b^24) - 111*(a^27*b^3 + a^3*b^27) + 61307748*(a^16*b^13 + a^13*b^16) - 6802212*(a^19*b^10 + a^10*b^19) + 3547332*(a^22*b^7 + a^7*b^22) - 14454*(a^25*b^4 + a^4*b^25) + 2*(a^28*b + a*b^28) - 20543742*(a^17*b^11 + a^11*b^17) + 11686473*(a^20*b^8 + a^8*b^20) - 654903*(a^23*b^5 + a^5*b^23) + 900*(a^26*b^2 + a^2*b^26) - 71710665*(a^15*b^12 + a^12*b^15) + 619563*(a^18*b^9 + a^9*b^18) - 6378348*(a^21*b^6 + a^6*b^21) + 35169*(a^24*b^3 + a^3*b^24) + 10*(a^27 + b^27) + 42911055*(a^16*b^10 + a^10*b^16) - 13616811*(a^19*b^7 + a^7*b^19) + 1428246*(a^22*b^4 + a^4*b^22) - 3087*(a^25*b + a*b^25) + 42632676*(a^14*b^11 + a^11*b^14) + 11786445*(a^17*b^8 + a^8*b^17) + 7671051*(a^20*b^5 + a^5*b^20) - 51516*(a^23*b^2 + a^2*b^23) - 61474764*(a^15*b^9 + a^9*b^15) + 9627636*(a^18*b^6 + a^6*b^18) - 1955076*(a^21*b^3 + a^3*b^21) + 3234*(a^24 + b^24) + 18467487*(a^13*b^10 + a^10*b^13) - 22792653*(a^16*b^7 + a^7*b^16) - 5784867*(a^19*b^4 + a^4*b^19) + 38619*(a^22*b + a*b^22) + 61988823*(a^14*b^8 + a^8*b^14) - 1706364*(a^17*b^5 + a^5*b^17) + 1613106*(a^20*b^2 + a^2*b^20) - 68733681*(a^12*b^9 + a^9*b^12) + 25013703*(a^15*b^6 + a^6*b^15) + 1851444*(a^18*b^3 + a^3*b^18) + 3891*(a^21 + b^21) + 59049*a^20*b^20 - 39246048*(a^13*b^7 + a^7*b^13) - 3473559*(a^16*b^4 + a^4*b^16) - 617145*(a^19*b + a*b^19) - 616734*a^19*b^19 + 83081628*(a^11*b^8 + a^8*b^11) - 14340744*(a^14*b^5 + a^5*b^14) + 1581399*(a^17*b^2 + a^2*b^17) + 2965572*a^18*b^18 + 18768948*(a^12*b^6 + a^6*b^12) + 5401068*(a^15*b^3 + a^3*b^15) + 128853*(a^18 + b^18) - 7358850*a^17*b^17 - 46052154*(a^10*b^7 + a^7*b^10) + 6781779*(a^13*b^4 + a^4*b^13) - 1378035*(a^16*b + a*b^16) + 9858600*a^16*b^16 + 1275939*(a^11*b^5 + a^5*b^11) - 1583091*(a^14*b^2 + a^2*b^14) + 2539437*a^15*b^15 + 12925416*(a^9*b^6 + a^6*b^9) + 604938*(a^12*b^3 + a^3*b^12) + 378687*(a^15 + b^15) - 40752756*a^14*b^14 - 4542219*(a^10*b^4 + a^4*b^10) - 609732*(a^13*b + a*b^13) + 92606436*a^13*b^13 + 6275295*(a^8*b^5 + a^5*b^8) - 2018205*(a^11*b^2 + a^2*b^11) - 118464618*a^12*b^12 + 2404647*(a^9*b^3 + a^3*b^9) + 406533*(a^12 + b^12) + 87497451*a^11*b^11 - 8983881*(a^7*b^4 + a^4*b^7) + 464892*(a^10*b + a*b^10) - 9768396*a^10*b^10 - 1303335*(a^8*b^2 + a^2*b^8) - 45026712*a^9*b^9 + 4193853*(a^6*b^3 + a^3*b^6) + 178827*(a^9 + b^9) + 66926439*a^8*b^8 + 576468*(a^7*b + a*b^7) - 44424837*a^7*b^7 - 887004*(a^5*b^2 + a^2*b^5) + 17471712*a^6*b^6 + 11253*(a^6 + b^6) - 3959892*a^5*b^5 + 226620*(a^4*b + a*b^4) - 117801*a^4*b^4 + 596433*a^3*b^3 - 10365*(a^3 + b^3) - 68508*a^2*b^2 + 2320*a*b + 1325),
      9*(a^3 + 1)*(b^3 + 1)*(3*a^2*b^2 + a^3 + b^3 - 3*a*b + 2)^12
   ];
end function;

function IgusaToAbsolute(L)
    J2:=L[1]; J4:=L[2]; J6:=L[3]; J8:=L[4]; J10:=L[5];
    return [J2^5/J10, J2^3*J4/J10, J2^2*J6/J10, J2*J8/J10, J4*J6/J10, J4*J8^2/J10^2, J6^2*J8/J10^2, J6^5/J10^3, J6*J8^3/J10^3, J8^5/J10^4];
end function;

function VerifyInvariants(a,b)
  if a^3 + 1 eq 0 then
    error "The curve defined by the first parameter is singular.";
  elif b^3 + 1 eq 0 then
    error "The curve defined by the second parameter is singular.";
  elif 3*a^2*b^2 + a^3 + b^3 - 3*a*b + 2 eq 0 then
    error "The 3-torsion isomorphism is induced by a 2-isogeny.";
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

  // The effective divisor on A that is linearly equivalent to 3Θ and fixed by [-1] and translation by A[3]
  D := Scheme(P8, [ X1 + X5 + X9 ]) meet A;  // or X2 + X4 + X9

  // points of A[2] that are the points of order 2 on E1 x {O} and {O} x E2, respectively
  E12 := Scheme(P8, [ 2*X5^3 + s*X5^2*X8 + X8^3, X1 + X5, X2 - X5, X3, X4 + X5, X6, X7 + X8, X9 ]);
  E22 := Scheme(P8, [ 2*X5^3 + t*X5^2*X6 + X6^3, X1 + X5, X2 + X5, X3 + X6, X4 - X5, X7, X8, X9 ]);

  // the composition A --> J=A/G --> J/[-1], followed by a projection that drops the first coordinate
  q := map< P8 -> P2 | [ X2*X4 + X3*X7 + X6*X8, X2*X3 + X4*X6 + X7*X8, X2*X8 + X3*X6 + X4*X7 ]>; // or [X1*X3 + X5*X6 + X7*X8, X1*X7 + X3*X6 + X5*X8, X1*X5 + X3*X8 + X6*X7]

  // H is the conic that is the image of C in J/[-1], projected to IP^2
  H := q(D);

  // B is the branch locus of the canonical map C --> H
  B := q(Union(E12,E22));

  // we find the inverse of the parametrization IP^1 --> H
  if IsReduced(H) then H:=Curve(H); end if;    // H is reduced; this is just a kludge to force Magma to actually find the curve.
  paramStrings := Split(Sprint(Parametrization(Conic(H))),"\n");
  coord1 := eval paramStrings[#paramStrings-1];
  coord2 := eval paramStrings[#paramStrings];
  paraminv := map< P2 -> P1 | [ coord1, coord2 ] >;

  // from the branch locus of the canonical map C --> IP^1, we recover C (up to quadratic twists)
  branch := paraminv(B);
  poly := Basis(Ideal(branch))[1];
  poly := Dehomogenize(poly);

  // we compare the actual Igusa-Clebsch invariants with our formula
  //return WP1!(IgusaClebschInvariants(HyperellipticCurve(poly))) eq  WP1!(ComputedIgusaClebschInvariants(a,b));
  return WP2!(IgusaInvariants(HyperellipticCurve(poly))) eq  WP2!(ComputedIgusaInvariants(a,b));
end function;

//examples
VerifyInvariants(1 + 2*w, 3/2 - w);
VerifyInvariants(2^20 + 7, 2^20 + 13);
