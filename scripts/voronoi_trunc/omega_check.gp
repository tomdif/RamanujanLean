\\ Max/min of S(x)/x^(23/4) on dyadic intervals; compare with 1/(2*Pi*sqrt(2)) = 0.1125 (evidence level 4).
default(nbthreads,1);
NM=40000; T=vector(NM,n,ramanujantau(n));
{ foreach([1000,2500,5000,10000,20000], X,
   my(s=sum(n=1,X,T[n]), mx=-1e9, mn=1e9);
   for(m=X, 2*X-1, if(m>X, s+=T[m]);
     \\ S is constant on [m, m+1); extremes of S/x^(23/4) on it are at the endpoints
     my(a=s/m^(23/4), b=s/(m+1)^(23/4)); mx=max(mx,max(a,b)); mn=min(mn,min(a,b)));
   printf("X=%6d  max S/x^(23/4) = % .4f   min = % .4f   (1/(2 pi sqrt2) = %.4f)\n", X, mx, mn, 1/(2*Pi*sqrt(2)))); }
