/* w is a primitive third root of unity, i.e. 1 + w + w^2 = 0.
   The function VerifyInvariants(a,b) will verify that gluing elliptic curves E1: x^3 + y^3 + z^3 + 3 a x y z = 0 and 
   E2: x^3 + y^3 + z^3 + 3 b x y z = 0, whose identity element is O=[-1:1:0], along the 3-torsion via the isomorphism E1[3] --> E2[3]
   defined by  [-1:0:1] |--> [-1:0:1] and [-w:0:1] |--> [-w^2:0:1], results in the Jacobian of a genus-2 curve C whose Igusa-Clebsch invariants
   are given by ComputedInvariants(a,b), unless 3*a^2*b^2 + a^3 + b^3 - 3*a*b + 2 = 0, in which case the isomorphism E1[3] --> E2[3]
   is the resitriction of a 2-isogeny E1 --> E2.
   
   Given bounds on the degree of the invariants in terms of a and b (which can be obtained by computing them for large integral values
   of a and b), verifying the formula given by ComputedInvariants(a,b) is correct for sufficiently many cases proves their correctness.
*/

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
      144*(a + b - 1)^6*(a^2 + b^2 - a*b + a + b + 1)^6*(9*a^6*b^6 - 30*(a^7*b^4 + a^4*b^7) + a^8*b^2 + a^2*b^8 - 88*a^5*b^5 + 54*(a^6*b^3 + a^3*b^6) - 32*(a^7*b + a*b^7) + 65*a^4*b^4 - 104*(a^5*b^2 + a^2*b^5) + 40*(a^6 + b^6) + 44*a^3*b^3 + 100*(a^4*b + a*b^4) - 68*a^2*b^2 + 16*a^3 + 16*b^3 + 112*a*b - 20),
      -768*(a + b - 1)^12*(a^2 + b^2 - a*b + a + b + 1)^12*(729*(a^13*b^10 + a^10*b^13) - 972*(a^14*b^8 + a^8*b^14) + 1944*a^11*b^11 + 81*(a^15*b^6 + a^6*b^15) - 3969*(a^12*b^9 + a^9*b^12) + 6102*(a^13*b^7 + a^7*b^13) - 6021*a^10*b^10 - 1881*(a^14*b^5 + a^5*b^14) + 11529*(a^11*b^8 + a^8*b^11) + 114*(a^15*b^3 + a^3*b^15) - 17067*(a^12*b^6 + a^6*b^12) + 5328*a^9*b^9 + a^16*b + a*b^16 + 7808*(a^13*b^4 + a^4*b^13) - 14219*(a^10*b^7 + a^7*b^10) - 984*(a^14*b^2 + a^2*b^14) + 29166*(a^11*b^5 + a^5*b^11) + 21501*a^8*b^8 - 14243*(a^12*b^3 + a^3*b^12) + 14492*(a^9*b^6 + a^6*b^9) + 20*(a^15 + b^15) - 15956*(a^10*b^4 + a^4*b^10) + 2680*(a^13*b + a*b^13) - 34896*a^7*b^7 + 19308*(a^11*b^2 + a^2*b^11) + 19800*(a^8*b^5 + a^5*b^8) - 1600*(a^12 + b^12) + 980*(a^9*b^3 + a^3*b^9) + 52761*a^6*b^6 - 26790*(a^7*b^4 + a^4*b^7) - 9488*(a^10*b + a*b^10) + 17235*(a^8*b^2 + a^2*b^8) - 26424*a^5*b^5 + 17226*(a^6*b^3 + a^3*b^6) - 640*(a^9 + b^9) - 20080*(a^7*b + a*b^7) - 6923*a^4*b^4 - 10536*(a^5*b^2 + a^2*b^5) + 3112*(a^6 + b^6) + 3404*a^3*b^3 - 6172*(a^4*b + a*b^4) - 7284*a^2*b^2 + 2320*(a^3 + b^3) + 1712*a*b + 190),
      4096*(a + b - 1)^18*(a^2 - b*a + a + b^2 + b + 1)^18*(a^24 - 162*b^5*a^23 - 138*b^2*a^23 + 6561*b^10*a^22 + 12636*b^7*a^22 + 8109*b^4*a^22 + 1758*b*a^22 - 39366*b^12*a^21 - 138510*b^9*a^21 - 148176*b^6*a^21 - 55576*b^3*a^21 - 4520*a^21 + 59049*b^14*a^20 + 459270*b^11*a^20 + 937818*b^8*a^20 + 673440*b^5*a^20 + 146469*b^2*a^20 - 459270*b^13*a^19 - 2202066*b^10*a^19 - 3341034*b^7*a^19 - 1754034*b^4*a^19 - 198300*b*a^19 + 39366*b^15*a^18 + 1664307*b^12*a^18 + 5803110*b^9*a^18 + 7005421*b^6*a^18 + 2751412*b^3*a^18 + 58756*a^18 - 118098*b^17*a^17 - 454896*b^14*a^17 - 3534354*b^11*a^17 - 9043632*b^8*a^17 - 8948592*b^5*a^17 - 2756412*b^2*a^17 + 905418*b^16*a^16 + 2288574*b^13*a^16 + 4691655*b^10*a^16 + 7291170*b^7*a^16 + 5765400*b^4*a^16 + 1047258*b*a^16 + 39366*b^18*a^15 - 2981610*b^15*a^15 - 5794524*b^12*a^15 - 2794498*b^9*a^15 + 455070*b^6*a^15 - 922404*b^3*a^15 - 90920*a^15 + 59049*b^20*a^14 - 454896*b^17*a^14 + 5347377*b^14*a^14 + 8748840*b^11*a^14 - 2902320*b^8*a^14 - 11707326*b^5*a^14 - 3956232*b^2*a^14 - 459270*b^19*a^13 + 2288574*b^16*a^13 - 3045906*b^13*a^13 - 6525930*b^10*a^13 + 5040828*b^7*a^13 + 11428560*b^4*a^13 + 3159408*b*a^13 - 39366*b^21*a^12 + 1664307*b^18*a^12 - 5794524*b^15*a^12 - 7419323*b^12*a^12 - 4897294*b^9*a^12 - 9687918*b^6*a^12 - 8043346*b^3*a^12 - 627440*a^12 + 459270*b^20*a^11 - 3534354*b^17*a^11 + 8748840*b^14*a^11 + 19173930*b^11*a^11 + 8348526*b^8*a^11 + 675420*b^5*a^11 + 1254504*b^2*a^11 + 6561*b^22*a^10 - 2202066*b^19*a^10 + 4691655*b^16*a^10 - 6525930*b^13*a^10 - 26821770*b^10*a^10 - 16123014*b^7*a^10 + 1449480*b^4*a^10 + 2215680*b*a^10 - 138510*b^21*a^9 + 5803110*b^18*a^9 - 2794498*b^15*a^9 - 4897294*b^12*a^9 + 8067464*b^9*a^9 + 4124680*b^6*a^9 - 2197640*b^3*a^9 - 786176*a^9 + 937818*b^20*a^8 - 9043632*b^17*a^8 - 2902320*b^14*a^8 + 8348526*b^11*a^8 + 357678*b^8*a^8 + 783360*b^5*a^8 + 2430549*b^2*a^8 + 12636*b^22*a^7 - 3341034*b^19*a^7 + 7291170*b^16*a^7 + 5040828*b^13*a^7 - 16123014*b^10*a^7 - 12141936*b^7*a^7 - 1168542*b^4*a^7 + 108288*b*a^7 - 148176*b^21*a^6 + 7005421*b^18*a^6 + 455070*b^15*a^6 - 9687918*b^12*a^6 + 4124680*b^9*a^6 + 9939345*b^6*a^6 + 2317278*b^3*a^6 - 373400*a^6 - 162*b^23*a^5 + 673440*b^20*a^5 - 8948592*b^17*a^5 - 11707326*b^14*a^5 + 675420*b^11*a^5 + 783360*b^8*a^5 - 2171160*b^5*a^5 - 151464*b^2*a^5 + 8109*b^22*a^4 - 1754034*b^19*a^4 + 5765400*b^16*a^4 + 11428560*b^13*a^4 + 1449480*b^10*a^4 - 1168542*b^7*a^4 + 1073241*b^4*a^4 - 220380*b*a^4 - 55576*b^21*a^3 + 2751412*b^18*a^3 - 922404*b^15*a^3 - 8043346*b^12*a^3 - 2197640*b^9*a^3 + 2317278*b^6*a^3 + 139052*b^3*a^3 - 59888*a^3 - 138*b^23*a^2 + 146469*b^20*a^2 - 2756412*b^17*a^2 - 3956232*b^14*a^2 + 1254504*b^11*a^2 + 2430549*b^8*a^2 - 151464*b^5*a^2 - 274020*b^2*a^2 + 1758*b^22*a - 198300*b^19*a + 1047258*b^16*a + 3159408*b^13*a + 2215680*b^10*a + 108288*b^7*a - 220380*b^4*a - 25104*b*a + b^24 - 4520*b^21 + 58756*b^18 - 90920*b^15 - 627440*b^12 - 786176*b^9 - 373400*b^6 - 59888*b^3 + 580),
      -5308416*(a + 1)*(a^2 - a + 1)*(b + 1)*(a + b - 1)^24*(b^2 - b + 1)*(a^2 - b*a + a + b^2 + b + 1)^24*(9*b^4*a^28 + 2*b*a^28 - 27*b^6*a^27 - 111*b^3*a^27 + 10*a^27 + 2187*b^11*a^26 + 3483*b^8*a^26 + 1818*b^5*a^26 + 900*b^2*a^26 - 6561*b^13*a^25 - 35964*b^10*a^25 - 39564*b^7*a^25 - 14454*b^4*a^25 - 3087*b*a^25 + 19683*b^15*a^24 + 114453*b^12*a^24 + 273753*b^9*a^24 + 190272*b^6*a^24 + 35169*b^3*a^24 + 3234*a^24 - 207765*b^14*a^23 - 775413*b^11*a^23 - 1283679*b^8*a^23 - 654903*b^5*a^23 - 51516*b^2*a^23 + 1034694*b^13*a^22 + 2826423*b^10*a^22 + 3547332*b^7*a^22 + 1428246*b^4*a^22 + 38619*b*a^22 - 19683*b^18*a^21 + 22599*b^15*a^21 - 3155760*b^12*a^21 - 6861459*b^9*a^21 - 6378348*b^6*a^21 - 1955076*b^3*a^21 + 3891*a^21 + 59049*b^20*a^20 + 395847*b^17*a^20 + 101574*b^14*a^20 + 6219855*b^11*a^20 + 11686473*b^8*a^20 + 7671051*b^5*a^20 + 1613106*b^2*a^20 - 616734*b^19*a^19 - 2817828*b^16*a^19 - 989883*b^13*a^19 - 6802212*b^10*a^19 - 13616811*b^7*a^19 - 5784867*b^4*a^19 - 617145*b*a^19 - 19683*b^21*a^18 + 2965572*b^18*a^18 + 12577788*b^15*a^18 + 6258405*b^12*a^18 + 619563*b^9*a^18 + 9627636*b^6*a^18 + 1851444*b^3*a^18 + 128853*a^18 + 395847*b^20*a^17 - 7358850*b^17*a^17 - 34004241*b^14*a^17 - 20543742*b^11*a^17 + 11786445*b^8*a^17 - 1706364*b^5*a^17 + 1581399*b^2*a^17 - 2817828*b^19*a^16 + 9858600*b^16*a^16 + 61307748*b^13*a^16 + 42911055*b^10*a^16 - 22792653*b^7*a^16 - 3473559*b^4*a^16 - 1378035*b*a^16 + 19683*b^24*a^15 + 22599*b^21*a^15 + 12577788*b^18*a^15 + 2539437*b^15*a^15 - 71710665*b^12*a^15 - 61474764*b^9*a^15 + 25013703*b^6*a^15 + 5401068*b^3*a^15 + 378687*a^15 - 207765*b^23*a^14 + 101574*b^20*a^14 - 34004241*b^17*a^14 - 40752756*b^14*a^14 + 42632676*b^11*a^14 + 61988823*b^8*a^14 - 14340744*b^5*a^14 - 1583091*b^2*a^14 - 6561*b^25*a^13 + 1034694*b^22*a^13 - 989883*b^19*a^13 + 61307748*b^16*a^13 + 92606436*b^13*a^13 + 18467487*b^10*a^13 - 39246048*b^7*a^13 + 6781779*b^4*a^13 - 609732*b*a^13 + 114453*b^24*a^12 - 3155760*b^21*a^12 + 6258405*b^18*a^12 - 71710665*b^15*a^12 - 118464618*b^12*a^12 - 68733681*b^9*a^12 + 18768948*b^6*a^12 + 604938*b^3*a^12 + 406533*a^12 + 2187*b^26*a^11 - 775413*b^23*a^11 + 6219855*b^20*a^11 - 20543742*b^17*a^11 + 42632676*b^14*a^11 + 87497451*b^11*a^11 + 83081628*b^8*a^11 + 1275939*b^5*a^11 - 2018205*b^2*a^11 - 35964*b^25*a^10 + 2826423*b^22*a^10 - 6802212*b^19*a^10 + 42911055*b^16*a^10 + 18467487*b^13*a^10 - 9768396*b^10*a^10 - 46052154*b^7*a^10 - 4542219*b^4*a^10 + 464892*b*a^10 + 273753*b^24*a^9 - 6861459*b^21*a^9 + 619563*b^18*a^9 - 61474764*b^15*a^9 - 68733681*b^12*a^9 - 45026712*b^9*a^9 + 12925416*b^6*a^9 + 2404647*b^3*a^9 + 178827*a^9 + 3483*b^26*a^8 - 1283679*b^23*a^8 + 11686473*b^20*a^8 + 11786445*b^17*a^8 + 61988823*b^14*a^8 + 83081628*b^11*a^8 + 66926439*b^8*a^8 + 6275295*b^5*a^8 - 1303335*b^2*a^8 - 39564*b^25*a^7 + 3547332*b^22*a^7 - 13616811*b^19*a^7 - 22792653*b^16*a^7 - 39246048*b^13*a^7 - 46052154*b^10*a^7 - 44424837*b^7*a^7 - 8983881*b^4*a^7 + 576468*b*a^7 - 27*b^27*a^6 + 190272*b^24*a^6 - 6378348*b^21*a^6 + 9627636*b^18*a^6 + 25013703*b^15*a^6 + 18768948*b^12*a^6 + 12925416*b^9*a^6 + 17471712*b^6*a^6 + 4193853*b^3*a^6 + 11253*a^6 + 1818*b^26*a^5 - 654903*b^23*a^5 + 7671051*b^20*a^5 - 1706364*b^17*a^5 - 14340744*b^14*a^5 + 1275939*b^11*a^5 + 6275295*b^8*a^5 - 3959892*b^5*a^5 - 887004*b^2*a^5 + 9*b^28*a^4 - 14454*b^25*a^4 + 1428246*b^22*a^4 - 5784867*b^19*a^4 - 3473559*b^16*a^4 + 6781779*b^13*a^4 - 4542219*b^10*a^4 - 8983881*b^7*a^4 - 117801*b^4*a^4 + 226620*b*a^4 - 111*b^27*a^3 + 35169*b^24*a^3 - 1955076*b^21*a^3 + 1851444*b^18*a^3 + 5401068*b^15*a^3 + 604938*b^12*a^3 + 2404647*b^9*a^3 + 4193853*b^6*a^3 + 596433*b^3*a^3 - 10365*a^3 + 900*b^26*a^2 - 51516*b^23*a^2 + 1613106*b^20*a^2 + 1581399*b^17*a^2 - 1583091*b^14*a^2 - 2018205*b^11*a^2 - 1303335*b^8*a^2 - 887004*b^5*a^2 - 68508*b^2*a^2 + 2*b^28*a - 3087*b^25*a + 38619*b^22*a - 617145*b^19*a - 1378035*b^16*a - 609732*b^13*a + 464892*b^10*a + 576468*b^7*a + 226620*b^4*a + 2320*b*a + 10*b^27 + 3234*b^24 + 3891*b^21 + 128853*b^18 + 378687*b^15 + 406533*b^12 + 178827*b^9 + 11253*b^6 - 10365*b^3 + 1325),
      9437184*(a + 1)*(a^2 - a + 1)*(b + 1)*(b^2 - b + 1)*(a + b - 1)^30*(a^2 + b^2 - a*b + a + b + 1)^30*(3*a^2*b^2 + a^3 + b^3 - 3*a*b + 2)^12
   ];
end function;

function IgusaToAbsolute(L)
    J2:=L[1]; J4:=L[2]; J6:=L[3]; J8:=L[4]; J10:=L[6];
    return [J2^5/J10, J2^3*J4/J10, J2^2*J6/J10, J2*J8/J10, J4*J6/J10, J4*J8^2/J10^2, J6^2*J8/J10^2, J6^5/J10^3, J6*J8^3/J10^3, J8^5/J10^4];
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
