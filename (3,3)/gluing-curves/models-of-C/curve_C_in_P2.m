function MyCurve(a,b)
  K1 := Parent(a);
  K2 := Parent(b);
  // Check for basic errors and initialize the setup.
  if Type(a) eq RngIntElt then K1:=Rationals(); end if;
  if Type(b) eq RngIntElt then K2:=Rationals(); end if;
  if IsField(K1) and IsField(K2) then
    if K1 eq K2 then
      K:=K1;
    else
	e1:=false; e2:=false;
	try
	  if IsSubfield(K1,K2) then K:=K2; end if;
	catch e
	  e1:=true;
	end try;
	try
	  if IsSubfield(K2,K1) then K:=K1; end if;
	catch e
	  e2:=true;
	end try;
	if e1 and e2 then
	  error "Cannot compare fields: ", K1, " and ", K2;
	end if;
    end if;
  else	
    error "Bad input type for parameters a and b ", "(", Type(a), ", ", Type(b), ")";
  end if;
  if a^3 + 1 eq 0 and b^3 + 1 eq 0 then
    error "The curves defined by both parameters are singular.";
  elif a^3 + 1 eq 0 then
    error "The curve defined by the first parameter is singular.";
  elif b^3 + 1 eq 0 then
    error "The curve defined by the second parameter is singular.";
  elif 3*a^2*b^2 + a^3 + b^3 - 3*a*b + 2 eq 0 then
    error "The 3-torsion isomorphism is induced by a 2-isogeny.";
  end if;
  R<x> := PolynomialRing(K);
  f := Factorization(x^2+x+1);
  if #f eq 2 then
    L := K;
    w := K!(x - f[1][1]);
  else
    L<w> := ext<K | x^2 + x + 1>;
  end if;
  a:=L!a; b:=L!b;
  R<x> := PolynomialRing(L);
  if a eq 1/2 and b eq 1/2 then
    return HyperellipticCurve((x^3 + 6*x^2 + 9*x + 36)*(x^3 - 6*x^2 + 9*x - 36));
  elif (a eq 1/2*w and b eq 1/2*w^2) or (a eq 1/2*w^2 and b eq 1/2*w) then
    return HyperellipticCurve(x^6 + 6*x^4 - 39*x^2 + 48);
  end if;
  if a + b eq 1 then
    return HyperellipticCurve(((a^2 - a + 1)^2*x^3 - 6*(a - 1)*(a^3 + 1)*x^2 + 3*(a - 2)*(4*a^2 - a - 2)*x - 6*(a^2 + 2*a - 2))*((a^2 - a + 1)^2*x^3 - 6*a*(a - 2)*(a^2 - a + 1)*x^2 - 3*(a + 1)*(4*a^2 - 7*a + 1)*x - 6*(a^2 - 4*a + 1)));
  elif a*w + b*w^2 eq 1 then
    return HyperellipticCurve((x^3 - 6*w*(a^2 - w)*x^2 + 3*w*(4*a^3 - 9*w^2*a^2 + 4)*x - 6*w*(a^2 + 2*a*w^2 - 2*w)*(a + 1)*(a + w))*(x^3 - 6*a*(a*w - 2)*x^2 - 3*w*(4*a^3 - 3*a^2*w^2 - 6*a*w + 1)*x - 6*w*(a + 1)*(a + w)*(a^2- 4*a*w^2 + w)));
  elif a*w^2 + b*w eq 1 then
    return HyperellipticCurve((x^3 - 6*w*(b^2 - w)*x^2 + 3*w*(4*b^3 - 9*w^2*b^2 + 4)*x - 6*w*(b^2 + 2*b*w^2 - 2*w)*(b + 1)*(b + w))*(x^3 - 6*b*(b*w - 2)*x^2 - 3*w*(4*b^3 - 3*b^2*w^2 - 6*b*w + 1)*x - 6*w*(b + 1)*(b + w)*(b^2- 4*b*w^2 + w)));
    // or replace w by w^2 in the previous one, which gives an isomorphic curve via (x,y) --> (w^2*x,y)
  else
    return HyperellipticCurve(1/3/(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)*( 
		(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)^2*x^3
		 - 3*(2*a + a^4 + 3*b^2 - 2*a*b^3)*(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)*x^2
		 - 9*(-1 + a*b)*(a + b^2)*(a + 2*a^4 + 3*a^2*b + 3*b^2 - a*b^3)*x
		 - (-1 + 4*a^3 + 6*a*b + 3*a^2*b^2 + 4*b^3)*(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)
	  )*(
		(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)*(-1 + 4*a^3 + 6*a*b + 3*a^2*b^2 + 4*b^3)*x^3
		 - 9*(a^2 + b)*(-1 + a*b)*(-3*a^2 - b + a^3*b - 3*a*b^2 - 2*b^4)*x^2
	 	 - 3*(2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)*(-3*a^2 - 2*b + 2*a^3*b - b^4)*x
	 	 - (2 + a^3 - 3*a*b + 3*a^2*b^2 + b^3)^2
	  ));
  end if;
end function;

// examples:
MyCurve(0,0);
MyCurve(2,2);
MyCurve(1,2);
