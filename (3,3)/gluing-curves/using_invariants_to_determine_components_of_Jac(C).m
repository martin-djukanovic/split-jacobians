/*  Given a genus-2 curve C: y^2 = f(x), whose Jacobian is known to be (3,3)-isogenous to some E1 x E2, what are the j-invariants E1 and E2?
    We apply this to an interesting curve, namely C: y^2 = x(2x^2+4x+3)(3x^2+4x+2). This curve has an involution given by (x,y) -> (1/x,y/x^3)
    (Examples 3.5 and 5.11).
*/
function HasSplitJac33(C)
    K :=  BaseField(C);
    ic := IgusaClebschInvariants(C);
    /* We equate, up to multiplication by a non-zero scalar u with the corresponding weights, the invariants of C with our formulas
       We equate j1 and j2 with the corresponding formulas in terms of a and b, respectively and then we eliminate a,b,u,
       leaving the j-invariants of the two complementary curves, if they exist. */
    R<u,a,b,j1,j2> := PolynomialRing(K,5);
    I:=ideal<R|[
      // Igusa-Clebsch invariants of C
      -u*ic[1] + 72*(-20 + 16*a^3 + 40*a^6 + 112*a*b + 100*a^4*b - 32*a^7*b - 68*a^2*b^2 - 104*a^5*b^2 + a^8*b^2 + 16*b^3 + 44*a^3*b^3 + 54*a^6*b^3 + 100*a*b^4 + 65*a^4*b^4 - 30*a^7*b^4 - 104*a^2*b^5 - 88*a^5*b^5 + 40*b^6 + 54*a^3*b^6 + 9*a^6*b^6 - 32*a*b^7 - 30*a^4*b^7 + a^2*b^8),
      -u^2*ic[2] + 36*(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)^4*(320 + 160*a^3 + 256*a*b + 8*a^4*b + 240*a^2*b^2 + 160*b^3 + 240*a^3*b^3 + 8*a*b^4 + 9*a^4*b^4),
      -u^3*ic[3] + 72*(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)^4*(-55040 + 74624*a^3 + 219552*a^6 + 84224*a^9 - 8*a^12 + 314112*a*b + 564480*a^4*b + 181152*a^7*b - 50160*a^10*b + 88512*a^2*b^2 - 93600*a^5*b^2 - 167112*a^8*b^2 + 480*a^11*b^2 + 74624*b^3 + 383424*a^3*b^3 + 455568*a^6*b^3 + 156928*a^9*b^3 + 60*a^12*b^3 + 564480*a*b^4 + 761040*a^4*b^4 + 81072*a^7*b^4 - 121608*a^10*b^4 - 93600*a^2*b^5 - 462096*a^5*b^5 - 358740*a^8*b^5 - 2160*a^11*b^5 + 219552*b^6 + 455568*a^3*b^6 + 336444*a^6*b^6 + 106560*a^9*b^6 + 81*a^12*b^6 + 181152*a*b^7 + 81072*a^4*b^7 - 148932*a^7*b^7 - 70794*a^10*b^7 - 167112*a^2*b^8 - 358740*a^5*b^8 - 201555*a^8*b^8 - 3402*a^11*b^8 + 84224*b^9 + 156928*a^3*b^9 + 106560*a^6*b^9 + 30456*a^9*b^9 - 50160*a*b^10 - 121608*a^4*b^10 - 70794*a^7*b^10 + 729*a^10*b^10 + 480*a^2*b^11 - 2160*a^5*b^11 - 3402*a^8*b^11 - 8*b^12 + 60*a^3*b^12 + 81*a^6*b^12),
      -u^5*ic[4] + 36864*(1 + a^3)*(1 + b^3)*(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)^12,
      // j-invariants of E1 and E2
      27*a^3*(-8 + a^3)^3 + j1 * (1 + a^3)^3,
      27*b^3*(-8 + b^3)^3 + j2 * (1 + b^3)^3
    ]>;
    J:=Radical(EliminationIdeal(I,3));
    B:=Basis(PrimaryDecomposition(J)[1]);
    if #B eq 0 then
        return false;
    else
        return true, {K!(j1 - B[1]), K!(j2-B[2])};
    end if;
end function;

R<x> := PolynomialRing(Rationals());
C := HyperellipticCurve(x*(2*x^2 + 4*x + 3)*(3*x^2 + 4*x + 2));
HasSplitJac33(C);
