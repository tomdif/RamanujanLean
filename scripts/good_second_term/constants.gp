default(nbthreads,1); default(parisizemax,2*10^9); default(realprecision,38);
\\ Constants for Good's second term.  a(n) = tau(n)/n^(11/2),  D(s) = sum a(n)^2 n^-s = zeta(s) L(sym^2,s)/zeta(2s).
\\ sym^2 Delta in arithmetic normalisation: L_ar(s) = L_an(s-11), integer coefficients, Gamma_R(s-10)Gamma_R(s)Gamma_R(s+1), weight 23.
N0=30000;
tv=mfcoefs(mfDelta(),N0);  \\ tv[n+1] = tau(n)
an=direuler(p=2,N0, my(t=tv[p+1]^2-p^11); 1/(1-t*X+p^11*t*X^2-p^33*X^3));
L2=lfuncreate([an,0,[-10,0,1],23,1,1]);
print("lfuncheckfeq(sym2) = ",lfuncheckfeq(L2));
Ls1=lfun(L2,12); Lp1=lfun(L2,12,1);
c0=Ls1/zeta(2);
gD=c0*(Euler+Lp1/Ls1-2*zeta'(2)/zeta(2));
print("c0 = L(sym2,1)/zeta(2) = ",c0);
print("gamma_D = Laurent constant of D at 1 = ",gD);
S=0.; for(n=1,N0, S+=tv[n+1]^2/n^12); print("partial sum check sum_{n<=N} a(n)^2/n - c0 log N (N=",N0,") = ",S-c0*log(N0));
print("int_0^T |L(Delta,6+it)|^2 = 2 c0 T log(T/2pi) + (2gD-2c0) T + o(T):  2c0 = ",2*c0,"   2gD-2c0 = ",2*gD-2*c0);
print("as 2c0 T log T + c1 T:  c1 = ",2*gD-2*c0-2*c0*log(2*Pi));
print("Good's form 2c0 T (log(T/(2 pi e)) + C): C = gD/c0 = ",gD/c0);
