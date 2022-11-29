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
	PD:=PrimaryDecomposition(J);
    if #PD eq 0 then
        return false;
    else
	B:=Basis(PD[1]);
    end if;
    if Degree(B[1]) eq 1 and Degree(B[2]) eq 1 then
	return true, {K!(j1 - B[1]), K!(j2 - B[2])};
    else
        return true, B;
    end if;
end function;

R<x>:=PolynomialRing(QQ);
C:=HyperellipticCurve((x^3+1)*(4*x^3+1));
HasSplitJac22(C);
