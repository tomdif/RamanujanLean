\\ Numerical checks for docs/VORONOI_TRUNC_GENERAL.md (evidence level 4).
\\ Weight k = 16 (f = Delta*E4) and k = 18 (f = Delta*E6): the sign of the Voronoi main term
\\ x^{(k-1)/2+1/4}/(pi sqrt2) sum a(n) n^{-(k/2+1/4)} cos(4 pi sqrt(nx) - pi/4), and the Cramer constant.
default(nbthreads,1); default(realprecision,38);
NM=20000;
coefs(k)={ my(q='q+O('q^(NM+1)), D=eta(q)^24*q, E=if(k==16, 1+240*sum(n=1,NM,sigma(n,3)*q^n), 1-504*sum(n=1,NM,sigma(n,5)*q^n)), F=D*E);
  vector(NM,n,polcoef(F,n,'q)) };
\\ path kernel vs Bessel J and the asymptotic with the i^k sign
Ik(nu,lam) = imag(intnum(s=0,[oo,1],(-1+I)*(1-s+I*s)^(-nu-1)*exp(lam*((1-s+I*s)-1/(1-s+I*s)))))/Pi;
{ foreach([16,18], nu, for(j=1,3, my(lam=5.*j^2);
   printf("nu=%d lam=%.1f  Ik=%.10g  J_nu(2lam)=%.10g  (-1)^(nu/2)cos(2lam-pi/4)/sqrt(pi lam)=%.10g\n",
     nu, lam, Ik(nu,lam), besselj(nu,2*lam), (-1)^(nu/2)*cos(2*lam-Pi/4)/sqrt(Pi*lam)))); }
{ foreach([16,18], nu, foreach([500.,2000.,8000.], lam,
   printf("nu=%d lam=%d  J_nu(2lam)*sqrt(pi lam)=%.6f   (-1)^(nu/2)cos(2lam-pi/4)=%.6f\n", nu, lam,
     besselj(nu,2*lam)*sqrt(Pi*lam), (-1)^(nu/2)*cos(2*lam-Pi/4)))); }
L2(T,k,X,N,sg)={ my(a=0.,b=0.,st=0.25, cs=vector(N,n,T[n]*n^(-(k/2+1/4))), s=sum(n=1,floor(X),T[n]), m=floor(X), e=(k-1)/2+1/4);
  forstep(x=X+st/2, 2*X, st, while(m+1<=x, m++; s+=T[m]);
    my(v=sg*sum(n=1,N,cs[n]*cos(4*Pi*sqrt(n*x)-Pi/4))/(Pi*sqrt(2)), ss=s/x^e);
    a+=(ss-v)^2*st; b+=ss^2*st);
  [a/X, b/X] };
run(k)={ my(T=coefs(k), B=sum(n=1,NM,T[n]^2*n^(-(k+1/2))));
   printf("k=%d a(1..4)=%s  B=%.6f  B/(4pi^2)=%.6f  Cramer const B/((4k+2)pi^2)=%.6g\n", k, T[1..4], B, B/(4*Pi^2), B/((4*k+2)*Pi^2));
   foreach([[2000.,20],[2000.,60],[8000.,40],[8000.,120]], p,
     my(rp=L2(T,k,p[1],p[2],1), rm=L2(T,k,p[1],p[2],-1));
     printf("  X=%d N=%d: mean (S-V)^2/x^(k-1/2) sign+ %.5f  sign- %.5f   mean S^2/x^(k-1/2)=%.5f\n", p[1],p[2],rp[1],rm[1],rp[2]));
   foreach([4000,16000], X, my(s=0., I2=0.); for(n=1,X-1, s+=T[n]; I2+=s^2);
     printf("  X=%d  X^{-(k+1/2)} int_1^X S^2 = %.6g\n", X, I2/X^(k+1/2)));
   my(mx=-1e9,mn=1e9,s=0.,e=(k-1)/2+1/4); for(n=1,16000, s+=T[n]; if(n>=8000, mx=max(mx,s/(n+0.)^e); mn=min(mn,s/(n+1.)^e)));
   printf("  on [8000,16000]: max S/x^e=%.4f  min S/x^e=%.4f  (Ingham constant 1/(2pi sqrt2)=%.4f)\n", mx, mn, 1/(2*Pi*sqrt(2))); }
run(16); run(18);
