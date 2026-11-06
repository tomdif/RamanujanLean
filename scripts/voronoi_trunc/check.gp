\\ Numerical checks for docs/VORONOI_TRUNC.md (evidence level 4).
default(nbthreads,1); default(realprecision,38);
\\ (1) path kernel  Ik(nu,lam) = (1/pi) Im int_0^oo (-1+I) v^(-nu-1) exp(lam(v-1/v)) ds, v=1-s+I s
Ik(nu,lam) = imag(intnum(s=0,[oo,1],(-1+I)*(1-s+I*s)^(-nu-1)*exp(lam*((1-s+I*s)-1/(1-s+I*s)))))/Pi;
{ for(j=1,4, my(lam=5.*j^2, nu=12);
   printf("Ik(%d,%.1f)=%.12g  besselj(nu,2lam)=%.12g  asym=%.12g\n", nu, lam, Ik(nu,lam),
     besselj(nu,2*lam), cos(2*lam-nu*Pi/2-Pi/4)/sqrt(Pi*lam))); }
\\ (2) truncated Voronoi in mean square
NM=40000; T=vector(NM,n,ramanujantau(n));
S(x)=sum(n=1,floor(x),T[n]);
V(x,N)=x^(23/4)/(Pi*sqrt(2))*sum(n=1,N,T[n]*n^(-25/4)*cos(4*Pi*sqrt(n*x)-Pi/4));
B=sum(n=1,NM,T[n]^2*n^(-25/2));
printf("B(partial)=%.6f  B/(4pi^2)=%.6f\n",B,B/(4*Pi^2));
{ my(X=10000.); forstep(x=X, X+5, 1.37, my(s=S(x));
   printf("x=%.2f S/x^(23/4)=% .5f  V_N/x^(23/4) (N=50,200,800)= % .5f % .5f % .5f\n", x, s/x^(23/4),
     V(x,50)/x^(23/4), V(x,200)/x^(23/4), V(x,800)/x^(23/4))); }
\\ L2 ratio over [X,2X] on a grid (Monte-Carlo-free midpoint rule, step 0.25)
L2(X,N)={ my(a=0.,b=0.,c=0.,st=0.25, cs=vector(N,n,T[n]*n^(-25/4)), s=S(X), m=floor(X));
  forstep(x=X+st/2, 2*X, st, while(m+1<=x, m++; s+=T[m]);
    my(v=sum(n=1,N,cs[n]*cos(4*Pi*sqrt(n*x)-Pi/4))/(Pi*sqrt(2)), w=x^(23/2), ss=s/x^(23/4));
    a+=(ss-v)^2*st; b+=ss^2*st; c+=v^2*st);
  [a/X, b/X, c/X] };
{ foreach([[2000.,20],[2000.,60],[8000.,30],[8000.,100],[16000.,40],[16000.,120]], p,
   my(r=L2(p[1],p[2])); printf("X=%d N=%d: mean (S-V)^2/x^(23/2)=%.5f  mean S^2/x^(23/2)=%.5f  mean V^2=%.5f\n",
     p[1],p[2],r[1],r[2],r[3])); }
