default(nbthreads,1);
default(realprecision,40);
L = lfuncreate(lfunmf(mfinit([1,12]), mfDelta()));
\\ alternatively ramanujantau-based ldata
L2 = lfuncreate([n->vector(n,k,ramanujantau(k)), 0, [0,1], 12, 1, 1]);
print("checkfeq: ", lfuncheckfeq(L2));
Lam(s) = (2*Pi)^(-s)*gamma(s)*lfun(L2,s);
foreach([3+2*I, 6+5*I, 1.3-0.7*I, 10+I], s, print("s=",s,"  |Lam(s)-Lam(12-s)| = ", abs(Lam(s)-Lam(12-s)), "  Lam(s)=", Lam(s)));
print("L(Delta,6) = ", lfun(L2,6));
print("Lam(6) = ", Lam(6), "  check 120(2pi)^-6 L(6) = ", 120*(2*Pi)^(-6)*lfun(L2,6));
print("Lam'(6) = ", lfun(L2,6,1)*(2*Pi)^(-6)*120 + 0, " (L'(6) times factor; Lam'(6) via numeric) ", (Lam(6+1e-10)-Lam(6-1e-10))/2e-10);
print("L(Delta,0),L(-1),L(-2) = ", lfun(L2,0), " ", lfun(L2,-1), " ", lfun(L2,-2));
\\ Mellin integral direct check at s=8
D(t) = suminf(n=1, ramanujantau(n)*exp(-2*Pi*n*t));
\\ positivity on real axis
print("L(Delta, sigma) for sigma in [-3.5,-0.5,0.5,3,6,9,12.5]: ", apply(x->lfun(L2,x), [-3.5,-0.5,0.5,3,6,9,12.5]));
print("Lam(sigma) : ", apply(x->Lam(x), [-3.5,-0.5,0.5,3,6,9,12.5]));
print("min Delta(it) on grid: ", vecmin(vector(40,k, my(t=0.05*k); real(sum(n=1,400,ramanujantau(n)*exp(-2*Pi*n*t))) + if(t<0.3, t^-12*real(sum(n=1,60,ramanujantau(n)*exp(-2*Pi*n/t))) - real(sum(n=1,400,ramanujantau(n)*exp(-2*Pi*n*t))), 0))));
\\ bound on Re s = 4
C = (2*Pi)^(-4)*sum(n=1,20000,abs(ramanujantau(n))*n^(-8.));
foreach([10,100,1000], T, my(s=4+T*I); print("T=",T," |L(4+iT)| = ", abs(lfun(L2,s)), "  bound ", C*abs(11-s)*abs(10-s)*abs(9-s)*abs(8-s)));
