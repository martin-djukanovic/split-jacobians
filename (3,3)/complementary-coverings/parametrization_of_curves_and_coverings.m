// both coverings generic
K<a,b,c>:=FunctionField(QQ,3);
A2<x,y>:=AffineSpace(K,2);
P:=x^3+a*x^2+b*x+c;
Q:=4*c *x^3+ b^2* x^2 + 2* b *c *x + c^2;
C:=Curve(A2, -y^2 + P*Q);
D1:=a^2*b^2 - 4*b^3 - 4*a^3*c + 18*a*b*c - 27*c^2;
D2:=b^3 - 27*c^2;
E1:=Curve(A2, -y^2 + D1*x^3 + 2*(-a*b^2 + 6*a^2*c - 9*b*c)*x^2 + (b^2 - 12*a*c)*x + 4*c);
E2:=Curve(A2, -D2*y^2 + x^3 + (a*b^3 - 27*b^2*c + 54*a*c^2)*x^2 + (b^7 - 18*a*b^5*c + 54*a^2*b^3*c^2 + 189*b^4*c^2 - 972*a*b^2*c^3 + 729*a^2*c^4 + 729*b*c^4)*x - c*(2*b^3 - 9*a*b*c + 27*c^2)^3);
f1:=map<C->E1 | [x^2/(c + b*x + a*x^2 + x^3), -(((-2*c - b*x + x^3)*y)/(c + b*x + a*x^2 + x^3)^2)]>;
f2:=map<C->E2 | [((3*c + b*x)^2*(b^2*c - 3*a*c^2 + b^3*x - 4*a*b*c*x + 9*c^2*x))/(c^2 + 2*b*c*x + b^2*x^2 + 4*c*x^3), (D2*(c^3 + b*c^2*x - b^2*c*x^2 + 4*a*c^2*x^2 - b^3*x^3 + 4*a*b*c*x^3 - 8*c^2*x^3)*y)/(c^2 + 2*b*c*x + b^2*x^2 + 4*c*x^3)^2]>;


// one covering generic, one covering special
K<b,c>:=FunctionField(QQ,2);
A2<x,y>:=AffineSpace(K,2);
P:=(b*x + 3*c)*(9*c*x^2+ 2*b^2*x + 3*b*c);
Q:=4*c*x^3+ b^2* x^2 + 2* b *c *x + c^2;
C:=Curve(A2, -y^2 + P*Q);
D:=b^3 - 27*c^2;
E1:=Curve(A2, -9*b*y^2 + 4*D^3*x^3 + 12*D^2*x^2 - 3*(5*b^3 + 108*c^2)*x + 4);
E2:=Curve(A2, -y^2 + c*x^3 + 2*D*x^2 - 27*c*D*x);
f1:=map<C->E1 | [x^2/((3*c + b*x)*(3*b*c + 2*b^2*x + 9*c*x^2)), -((9*b*c*(-2*c - b*x + x^3)*y)/((3*c + b*x)^2*(3*b*c + 2*b^2*x + 9*c*x^2)^2))]>;
f2:=map<C->E2 | [(3*c + b*x)^3/(c^2 + 2*b*c*x + b^2*x^2 + 4*c*x^3), -(((3*c + b*x)*(3*b*c^2 + 2*b^2*c*x - b^3*x^2 + 36*c^2*x^2)*y)/(c^2 + 2*b*c*x + b^2*x^2 + 4*c*x^3)^2)]>;

// both coverings special
K<b>:=FunctionField(QQ);
A2<x,y>:=AffineSpace(K,2);
P:=x^2+b;
Q:=x*(4*x^2+3*b);
C:=Curve(A2, -y^2 + P*Q);
E1:=Curve(A2,  - y^2 + 9*b^3*x^3 + 9*x);
E2:=Curve(A2, -y^2 + 4*x^3 + 27*b*x );
f1:=map<C->E1 | [1/(x*(3*b + 4*x^2)), -((3*(b + 4*x^2)*y)/(x^2*(3*b + 4*x^2)^2))]>;
f2:=map<C->E2 | [x^3/(b + x^2), (x*(3*b + x^2)*y)/(b + x^2)^2]>;
