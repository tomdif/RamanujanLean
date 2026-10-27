// p(n) mod M for n<=NMAX via Euler pentagonal recurrence; writes binary int64 array
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc,char**argv){
  long NMAX=atol(argv[1]); int64_t M=atoll(argv[2]); const char*out=argv[3];
  int64_t*p=malloc(sizeof(int64_t)*(NMAX+1));
  // pentagonal numbers
  long K=0; while((long)(K+1)*(3*(K+1)-1)/2<=NMAX) K++;
  long *g1=malloc(sizeof(long)*(K+2)),*g2=malloc(sizeof(long)*(K+2));
  for(long k=1;k<=K+1;k++){g1[k]=k*(3*k-1)/2; g2[k]=k*(3*k+1)/2;}
  p[0]=1%M;
  for(long n=1;n<=NMAX;n++){
    int64_t s=0;
    for(long k=1;g1[k]<=n;k++){
      int64_t t=p[n-g1[k]]; if(g2[k]<=n) t+=p[n-g2[k]];
      if(k&1) s+=t; else s-=t;
      if(s>=4*M) s-=4*M; if(s<=-4*M) s+=4*M;
    }
    s%=M; if(s<0) s+=M; p[n]=s;
  }
  FILE*f=fopen(out,"wb"); fwrite(p,sizeof(int64_t),NMAX+1,f); fclose(f);
  return 0;
}
