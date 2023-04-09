// note: does not work in characteristic 2
function HasSplitJac22(C)
    K :=  BaseField(C);
    ii := IgusaInvariants(C);
    R<u,a,b,c,j1,j2> := PolynomialRing(K,6);
    II := [
        -32*a*b - 480*c,
        -128*a^3*c + 32*a^2*b^2 + 2624*a*b*c - 128*b^3 + 5280*c^2,
        -16384*a^3*c^2 + 4096*a^2*b^2*c - 57344*a*b*c^2 - 16384*b^3*c + 20480*c^3,
        -4096*a^6*c^2 + 2048*a^5*b^2*c - 256*a^4*b^4 + 299008*a^4*b*c^2 - 82944*a^3*b^3*c + 2304000*a^3*c^3 + 2048*a^2*b^5 - 1838592*a^2*b^2*c^2 + 299008*a*b^4*c - 209920*a*b*c^3 - 4096*b^6 + 2304000*b^3*c^2 - 9427200*c^4,
        -262144*a^6*c^3 + 131072*a^5*b^2*c^2 - 16384*a^4*b^4*c + 2359296*a^4*b*c^3 - 1114112*a^3*b^3*c^2 - 3538944*a^3*c^4 + 131072*a^2*b^5*c - 4423680*a^2*b^2*c^3 + 2359296*a*b^4*c^2 + 15925248*a*b*c^4 - 262144*b^6*c - 3538944*b^3*c^3 - 11943936*c^5
    ];
    I:=ideal<R|
        [-u^k*II[k] + ii[k] : k in [1..5]] cat [
            256*(a^2 - 3*b)^3 + (-a^2*b^2 + 4*b^3 + 4*a^3*c - 18*a*b*c + 27*c^2)*j1,
            256*(b^2 - 3*a*c)^3 + c^2*(-a^2*b^2 + 4*b^3 + 4*a^3*c - 18*a*b*c + 27*c^2)*j2
        ]>;
    J:=Radical(EliminationIdeal(I,4));
    if J eq R then return false; end if;
    B:=Basis(PrimaryDecomposition(J)[1]);
    if #B eq 0 then
        return false;
    elif Degree(B[1]) eq 1 and Degree(B[2]) eq 1 then
        return true, [K!(j1 - B[1]), K!(j2 - B[2])];
    else return true, B;
    end if;
end function;

// examples
R<x>:=PolynomialRing(GF(3));
C:=HyperellipticCurve(x^6+x^4+x^2+1);
HasSplitJac22(C);

R<x>:=PolynomialRing(QQ);
C:=HyperellipticCurve((x^3+1)*(4*x^3+1));
HasSplitJac22(C);


// this version uses Igusa-Clebsch invariants so it is faster, but it does not work in characteristic 3
function HasSplitJac22(C)
    K :=  BaseField(C);
    ic := IgusaClebschInvariants(C);
    R<u,a,b,j1,j2> := PolynomialRing(K,5);
    I:=ideal<R|[
        -u*ic[1] + 8*(a*b + 15),
        -u^2*ic[2] + a^2*b^2 + 12*(a^3 + b^3) - 126*a*b + 405,
        -u^3*ic[3] + 3*a^3*b^3 + 20*(a^4*b + a*b^4) - 53*a^2*b^2 + 12*(a^3 + b^3) - 2583*a*b + 14985,
        -u^5*ic[4] + 2*(4*(a^3 + b^3) - a^2*b^2 - 18*a*b + 27)^2,
	j1*(4*a^3 + 4*b^3 - a^2*b^2 - 18*a*b + 27) + 256*(a^2 - 3*b)^3,
	j2*(4*a^3 + 4*b^3 - a^2*b^2 - 18*a*b + 27) + 256*(b^2 - 3*a)^3
    ]>;
    J:=Radical(EliminationIdeal(I,3));
    if J eq R then return false; end if;
    B:=Basis(PrimaryDecomposition(J)[1]);
    if #B eq 0 then
        return false;
    elif Degree(B[1]) eq 1 and Degree(B[2]) eq 1 then
        return true, [K!(j1 - B[1]), K!(j2 - B[2])];
    else return true, B;
    end if;
end function;
