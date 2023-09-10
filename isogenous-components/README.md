This code accompanies the paper _Families of split Jacobians with isogenous components_ (JTNB).

It is organized as follows:
- _general_strategy.m_ contains code that outputs the components of _S_<sub>*n*</sub>(*N*), defined in §3. It also verifies geometric irreducibility and computes the genera of the irreducible components (over Q for *n*=2 or Q(sqrt(-3)) for *n*=3). 
- _isogeny_induced_isogeny.m_ contains code that outputs the content of Table 1 and Table 2.
- _extra_splittings.m_ verifies the results of §4.4, showing that various curves described in the paper have a Jacobian that is not only (2,2)- or (3,3)- split, but also (*n,n*)- split for other values of *n*. This is based on the work of A.Kumar https://arxiv.org/abs/1412.2849.
- The folders (2,2) and (3,3) contain code that verifies that various curves _C_ described in the paper that have a (2,2)- or (3,3)- split Jacobian are such that the Jacobian has *N*-isogenous components for specific values of *N*, as claimed in the paper.
