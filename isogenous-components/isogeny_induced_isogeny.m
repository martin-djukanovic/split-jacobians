/*  This is a function that, given n and g=g(X0(N)), returns pairs <N,m> such that m^2*N = -1 (mod n)
    and the corresponding proper representation n=r*a^2+s*b^2 does not satisfy a=mbs (mod n).
    It is not a very efficient function, but it will do for small values of n.  */
function findN(n,g)
	if g eq 0 then
		S:=[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 16, 18, 25];
	elif g eq 1 then
		S:=[11, 14, 15, 17, 19, 20, 21, 24, 27, 32, 36, 49];
		// of this only  11, 14, 15, 17, 19, 21, 27  have (finitely many) Q-rational points
	end if;
	// factorizations of N corresponding to primitive diagonal forms of discriminant -4N
	fact:=[];
	fact[1]:=[<1,1>];
	fact[2]:=[<1,2>];
	fact[3]:=[<1,3>];
	fact[4]:=[<1,4>];
	fact[5]:=[<1,5>];
	fact[6]:=[<1,6>,<2,3>];
	fact[7]:=[<1,7>];
	fact[8]:=[<1,8>];
	fact[9]:=[<1,9>];
	fact[10]:=[<1,10>,<2,5>];
	fact[11]:=[<1,11>];
	fact[12]:=[<1,12>,<3,4>];
	fact[13]:=[<1,13>];
	fact[14]:=[<1,14>,<2,7>];
	fact[15]:=[<1,15>,<3,5>];
	fact[16]:=[<1,16>];
	fact[17]:=[<1,17>];
	fact[18]:=[<1,18>,<2,9>];
	fact[19]:=[<1,19>];
	fact[20]:=[<1,20>,<4,5>];
	fact[21]:=[<1,21>,<3,7>];
	fact[24]:=[<1,24>,<3,8>];
	fact[25]:=[<1,25>];
	fact[27]:=[<1,27>];
	fact[32]:=[<1,32>];
	fact[36]:=[<1,36>,<4,9>];
	fact[37]:=[<1,37>];
	fact[43]:=[<1,43>];
	fact[49]:=[<1,49>];
	L:=[];
	for N in S do
		if &and[JacobiSymbol(-N,f[1]) eq 1 : f in Factorization(n) | f[1] ne 2] and -N mod 2^Min(3,Valuation(n,2)) in {0,1} then
			for m in [1..Floor(n/2)] do
				if (m^2*N + 1) mod n eq 0 and GCD(N,n) eq 1 then
					f:=true; repr:=false;
					for ss in fact[N] do
						if f then
							r:=ss[1];
							s:=ss[2];
							for k in [1..n-1] do
								if k mod r eq 0 and (n-k) mod s eq 0 then
									A1:=ZZ!(k/r);
									A2:=ZZ!((n-k)/s);
									s1,a:=IsSquare(A1);
									s2,b:=IsSquare(A2);
									if s1 and s2 and GCD(a,b) eq 1 then
										repr:=true;
										if (b*s*m - a) mod n eq 0 or (b*s*m + a) mod n eq 0 then
											f:=false;
											break;
										end if;
									end if;
								end if;
							end for;
						end if;
					end for;
					if f then
						Append(~L,<N,m>);
					end if;
				end if;
			end for;
		end if;
	end for;
	return L;
end function;
for n in [1..42] do L:=findN(n,0); if #L ge 1 then print n,L; end if; end for; // genus 0 cases
for n in [1..30] do L:=findN(n,1); if #L ge 1 then print n,L; end if; end for; // genus 1 cases
