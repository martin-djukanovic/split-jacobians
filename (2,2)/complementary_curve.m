K<a,b,c,d>:=FunctionField(QQ,4);
P2<x,y,z>:=ProjectiveSpace(K,2);
P8<[X]>:=ProjectiveSpace(K,8);
C:=Curve(P2, -y^2*z^4 + a*x^6 + b*x^4*z^2 + c*x^2*z^4 + d*z^6);    // covers E1 via f1:(x,y)->(x^2,y) and E2 via f2:(x,y)->(1/x^2,y/x^3).
E1:=Curve(P2, -y^2*z + a*x^3 + b*x^2*z + c*x*z^2 + d*z^3);
E2:=Curve(P2, -y^2*z + d*x^3 + c*x^2*z + b*x*z^2 + a*z^3);

// we verify that E2 is the complement to E1 in Jac(C) over K
E2:=EllipticCurve(E2,E2![0,1,0]);
J:=SegreProduct([C,C]);
J:=map<AmbientSpace(J)->P8|[X]>(J);                                  // X = [xu : xv : xw : yu : yv : yw : zu : zv : zw]
KC := Scheme (P8, [X[2] + X[4], X[3] - X[7], X[6] + X[8]]) meet J;  // corresponds to the canonical class {(x,y),(x,-y)}; this is blown down
CC := Scheme (P8, [X[2] - X[4], X[3] + X[7], X[6] + X[8]]) meet J; // corresponds to Jac(C)/E1=Ker(f1_*)= {(x,y),(-x,-y)}; under f1 it gives (x^2,y)+(x^2,-y)=O on E1.
P3:=ProjectiveSpace(K,3);
g:=map<P8->P3|[X[1], X[5], X[2] + X[4], X[9]]>;    // this sends (x,y,u,v) to (u*x, v*y, v*x + u*y) = (-x^2, -y^2, -2*x*y), so that (x,y,u,v) and (u,v,x,y) have the same image
EE:=g(CC);                                        // the quotient of CC under the S2 action is the complementary curve
E:=EllipticCurve(Curve(EE),EE![0,-d,0,1]);       // EE![0,1,0,0] is singular and requires sqrt(a) to resolve
IsIsomorphic(E,E2);                             // the complementary curve is indeed E2 (and not a twist of it)
