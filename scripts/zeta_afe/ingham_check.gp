default(nbthreads,1); default(realprecision,20);
\\ I(T) = int_0^T |zeta(1/2+it)|^2 dt  vs  Ingham main term T log(T/2pi) + (2 Euler - 1) T
Iz(T)={my(s=0.); for(k=0,T-1, s+=intnum(t=k,k+1, abs(zeta(1/2+I*t))^2)); s};
{foreach([100,200,400],T, my(v=Iz(T), m=T*log(T/(2*Pi))+(2*Euler-1)*T);
  printf("T=%d I=%.3f Ingham=%.3f diff=%.3f diff/sqrt(T)=%.3f\n",T,v,m,v-m,(v-m)/sqrt(T)))}
