function ComputedIgusaClebsch44(x,y)
    return [ 2^3 * (4*x^12 + x^16 + 160*x^9*y - 208*x^13*y + 10*x^17*y + 64*x^6*y^2 - 600*x^10*y^2 + 
    660*x^14*y^2 + x^18*y^2 - 1408*x^7*y^3 + 2144*x^11*y^3 - 1008*x^15*y^3 + 640*x^4*y^4 + 
    4220*x^8*y^4 - 4940*x^12*y^4 + 660*x^16*y^4 - 2112*x^5*y^5 - 5680*x^9*y^5 + 
    6808*x^13*y^5 - 208*x^17*y^5 + 64*x^2*y^6 + 2736*x^6*y^6 + 3692*x^10*y^6 - 
    4940*x^14*y^6 + 4*x^18*y^6 - 1408*x^3*y^7 + 1344*x^7*y^7 - 2448*x^11*y^7 + 
    2144*x^15*y^7 + 4220*x^4*y^8 - 9578*x^8*y^8 + 3692*x^12*y^8 - 600*x^16*y^8 + 
    160*x*y^9 - 5680*x^5*y^9 + 14780*x^9*y^9 - 5680*x^13*y^9 + 160*x^17*y^9 - 
    600*x^2*y^10 + 3692*x^6*y^10 - 9578*x^10*y^10 + 4220*x^14*y^10 + 2144*x^3*y^11 - 
    2448*x^7*y^11 + 1344*x^11*y^11 - 1408*x^15*y^11 + 4*y^12 - 4940*x^4*y^12 + 
    3692*x^8*y^12 + 2736*x^12*y^12 + 64*x^16*y^12 - 208*x*y^13 + 6808*x^5*y^13 - 
    5680*x^9*y^13 - 2112*x^13*y^13 + 660*x^2*y^14 - 4940*x^6*y^14 + 4220*x^10*y^14 + 
    640*x^14*y^14 - 1008*x^3*y^15 + 2144*x^7*y^15 - 1408*x^11*y^15 + y^16 + 660*x^4*y^16 - 
    600*x^8*y^16 + 64*x^12*y^16 + 10*x*y^17 - 208*x^5*y^17 + 160*x^9*y^17 + x^2*y^18 + 4*x^6*y^18),
    
    2^2 * (16 - 16*x^4 + x^8 + 960*x*y - 840*x^5*y + 2160*x^2*y^2 - 
    1620*x^6*y^2 + 1680*x^3*y^3 - 840*x^7*y^3 - 16*y^4 + 1126*x^4*y^4 - 16*x^8*y^4 - 
    840*x*y^5 + 1680*x^5*y^5 - 1620*x^2*y^6 + 2160*x^6*y^6 - 840*x^3*y^7 + 960*x^7*y^7 + 
    y^8 - 16*x^4*y^8 + 16*x^8*y^8) * (x^2 - y^2)^4 * (x*y - 1)^4 * (x^4 - 4*x*y + 6*x^2*y^2 - 4*x^3*y^3 + y^4)^4,
          
    2^3 * (64*x^12 - 32*x^16 - 26*x^20 + x^24 + 3584*x^9*y - 256*x^13*y - 2016*x^17*y - 
    664*x^21*y + 14*x^25*y + 1024*x^6*y^2 + 169088*x^10*y^2 - 359936*x^14*y^2 + 
    197188*x^18*y^2 - 10210*x^22*y^2 + x^26*y^2 + 96256*x^7*y^3 - 471040*x^11*y^3 + 
    651264*x^15*y^3 - 241872*x^19*y^3 - 31640*x^23*y^3 + 14336*x^4*y^4 - 1362496*x^8*y^4 + 
    2567552*x^12*y^4 - 1228562*x^16*y^4 + 20350*x^20*y^4 - 10210*x^24*y^4 + 
    685056*x^5*y^5 + 397568*x^9*y^5 - 2250880*x^13*y^5 + 505416*x^17*y^5 + 
    651836*x^21*y^5 - 664*x^25*y^5 + 1024*x^2*y^6 - 1119488*x^6*y^6 + 3513344*x^10*y^6 - 
    3270352*x^14*y^6 + 935622*x^18*y^6 + 20350*x^22*y^6 - 26*x^26*y^6 + 96256*x^3*y^7 - 
    278528*x^7*y^7 - 4612096*x^11*y^7 + 8735296*x^15*y^7 - 3931192*x^19*y^7 - 
    241872*x^23*y^7 - 1362496*x^4*y^8 + 6629696*x^8*y^8 - 5757140*x^12*y^8 - 
    370881*x^16*y^8 + 935622*x^20*y^8 + 197188*x^24*y^8 + 3584*x*y^9 + 397568*x^5*y^9 - 
    5332800*x^9*y^9 + 6386768*x^13*y^9 - 1992046*x^17*y^9 + 505416*x^21*y^9 - 
    2016*x^25*y^9 + 169088*x^2*y^10 + 3513344*x^6*y^10 - 9029352*x^10*y^10 + 
    6728988*x^14*y^10 - 370881*x^18*y^10 - 1228562*x^22*y^10 - 32*x^26*y^10 - 
    471040*x^3*y^11 - 4612096*x^7*y^11 + 21560608*x^11*y^11 - 25649200*x^15*y^11 + 
    8735296*x^19*y^11 + 651264*x^23*y^11 + 64*y^12 + 2567552*x^4*y^12 - 5757140*x^8*y^12 - 
    42364*x^12*y^12 + 6728988*x^16*y^12 - 3270352*x^20*y^12 - 359936*x^24*y^12 - 
    256*x*y^13 - 2250880*x^5*y^13 + 6386768*x^9*y^13 - 8153528*x^13*y^13 + 
    6386768*x^17*y^13 - 2250880*x^21*y^13 - 256*x^25*y^13 - 359936*x^2*y^14 - 
    3270352*x^6*y^14 + 6728988*x^10*y^14 - 42364*x^14*y^14 - 5757140*x^18*y^14 + 
    2567552*x^22*y^14 + 64*x^26*y^14 + 651264*x^3*y^15 + 8735296*x^7*y^15 - 
    25649200*x^11*y^15 + 21560608*x^15*y^15 - 4612096*x^19*y^15 - 471040*x^23*y^15 - 
    32*y^16 - 1228562*x^4*y^16 - 370881*x^8*y^16 + 6728988*x^12*y^16 - 9029352*x^16*y^16 + 
    3513344*x^20*y^16 + 169088*x^24*y^16 - 2016*x*y^17 + 505416*x^5*y^17 - 
    1992046*x^9*y^17 + 6386768*x^13*y^17 - 5332800*x^17*y^17 + 397568*x^21*y^17 + 
    3584*x^25*y^17 + 197188*x^2*y^18 + 935622*x^6*y^18 - 370881*x^10*y^18 - 
    5757140*x^14*y^18 + 6629696*x^18*y^18 - 1362496*x^22*y^18 - 241872*x^3*y^19 - 
    3931192*x^7*y^19 + 8735296*x^11*y^19 - 4612096*x^15*y^19 - 278528*x^19*y^19 + 
    96256*x^23*y^19 - 26*y^20 + 20350*x^4*y^20 + 935622*x^8*y^20 - 3270352*x^12*y^20 + 
    3513344*x^16*y^20 - 1119488*x^20*y^20 + 1024*x^24*y^20 - 664*x*y^21 + 651836*x^5*y^21 + 
    505416*x^9*y^21 - 2250880*x^13*y^21 + 397568*x^17*y^21 + 685056*x^21*y^21 - 
    10210*x^2*y^22 + 20350*x^6*y^22 - 1228562*x^10*y^22 + 2567552*x^14*y^22 - 
    1362496*x^18*y^22 + 14336*x^22*y^22 - 31640*x^3*y^23 - 241872*x^7*y^23 + 
    651264*x^11*y^23 - 471040*x^15*y^23 + 96256*x^19*y^23 + y^24 - 10210*x^4*y^24 + 
    197188*x^8*y^24 - 359936*x^12*y^24 + 169088*x^16*y^24 + 1024*x^20*y^24 + 14*x*y^25 - 
    664*x^5*y^25 - 2016*x^9*y^25 - 256*x^13*y^25 + 3584*x^17*y^25 + x^2*y^26 - 
    26*x^6*y^26 - 32*x^10*y^26 + 64*x^14*y^26)*(x^2 - y^2)^4 * (x*y - 1)^4 * (x^4 - 4*x*y + 6*x^2*y^2 - 4*x^3*y^3 + y^4)^4,

   2^8 * x*y * (x^4 - 1) * (y^4 - 1) * (x*y - 1)^12 * (x^2 - y^2)^12 * (x^4 - 4*x*y + 6*x^2*y^2 - 4*x^3*y^3 + y^4)^12];
end function;

// Note: this is not particularly fast
function HasSplitJac44(C)
    K :=  BaseField(C);
    ic := IgusaClebschInvariants(C);
    R<u,a,b,j1,j2> := PolynomialRing(K,5);
    m:=ComputedIgusaClebsch44(a,b);
    I:=ideal<R|[
    // Igusa-Clebsch invariants of C
        - u*ic[1] + m[1],
      - u^2*ic[2] + m[2],
      - u^3*ic[3] + m[3],
      - u^5*ic[4] + m[4],
    // j-invariants of E1 and E2
       16*(a^8 + 14*a^4 + 1)^3 - a^4*(a^4 - 1)^4*j1,
       16*(b^8 + 14*b^4 + 1)^3 - b^4*(b^4 - 1)^4*j2
    ]>;
    J:=Radical(EliminationIdeal(I,3));
    if J eq R then return false; end if;
    L1:={}; L2:={};
    for P in PrimaryDecomposition(J) do
        B:=Basis(P);
        if #B ne 0 and Degree(B[1]) eq 1 and Degree(B[2]) eq 1 then
            Include(~L1, {K!(j1 - B[1]), K!(j2 - B[2])});
        else
            Include(~L2, B);
        end if;
    end for;
    L1:=[SetToSequence(s):s in L1];
    for k in [1..#L1] do
        if #L1[k] eq 1 then
            L1[k]:=[L1[k][1],L1[k][1]];
        end if;
    end for;
    if #L1 eq 0 and #L2 eq 0 then
        return false;
    elif #L1 ne 0 and #L2 eq 0 then
        return true, L1;
    elif #L2 ne 0 and #L1 eq 0 then
        return true, L2;
    else
        return true, <L1,L2>;
    end if;
end function;

F:=GF(41);
R<x>:=PolynomialRing(F);
C:=HyperellipticCurve(8*x^6 - 32*x^5 + 49*x^4 - 131*x^3 + 142*x^2 - 80*x + 16);
HasSplitJac44(C); //[F! -300763000000/3858407, F! -13679355439296/4149995543];
