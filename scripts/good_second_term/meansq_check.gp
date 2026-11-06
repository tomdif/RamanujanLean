default(nbthreads,1); default(realprecision,19);
\\ I(T) = int_0^T |L(Delta,6+it)|^2 dt  vs  2c0 T log(T/2pi) + (2gD-2c0) T   (constants from constants.gp)
c0=0.38408405446817036992636710674931703817; gD=0.79602825584793044651331756509910255024;
mf=mfinit([1,12],1); F=mfbasis(mf)[1]; LD=lfuncreate(lfunmf(mf,F));
Tmax=400; Li=lfuninit(LD,[6,0,Tmax+1]);
Iz(a,b)=intnum(t=a,b, abs(lfun(Li,6+I*t))^2);
acc=0.; prev=0;
{foreach([50,100,200,300,400],T, acc+=sum(k=prev,T-1,Iz(k,k+1)); prev=T;
  my(m=2*c0*T*log(T/(2*Pi))+(2*gD-2*c0)*T, m1=2*c0*T*log(T/(2*Pi)));
  printf("T=%d I=%.4f main=%.4f I-main=%.3f (I-main)/sqrt(T)=%.3f | without 2nd term: (I-2c0 T log(T/2pi))/T=%.4f\n",
    T,acc,m,acc-m,(acc-m)/sqrt(T),(acc-m1)/T))}
