/* Numerics for SKQFHyp (RamanujanTau/SelbergKey/Arith.lean).
   For Selberg's mollifier beta = alpha (1 - log n / log y), n <= y, computes on a v-grid
     S(v)  = sum_{a,b,c,d<=y} kap (P1 d/c)^{iv} rho(P1,1-iv) rho(Q1,1-iv)
     S0(v) = sum_{a,b,c,d<=y} kap (P1 d/c)^{iv} (P1 Q1)^{-iv/2} rho(P1) rho(Q1)
   kap = b(a)b(b)b(c)b(d)/[ac,bd], P=ac, Q=bd, g=(P,Q), P1=P/g, Q1=Q/g.
   Reduction: (P1 d/c) = a d / g, so with x_v(P) = sum_{ac=P} b(a)b(c) a^{iv},
     S(v) = sum_{P,Q} x_v(P) x_v(Q) g^{1-iv}/(PQ) rho(P1,1-iv) rho(Q1,1-iv).
   Usage: sk y vmax dv  > out ; columns: v ReS ImS ReS0 ImS0
   Needs taup.txt (p tau(p)) for p <= y^2.  */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <complex.h>
#define J 90
#define EMAX 40
typedef double complex cplx;
static int gcd(int a,int b){while(b){int t=a%b;a=b;b=t;}return a;}
int main(int argc,char**argv){
  int y=atoi(argv[1]); double vmax=atof(argv[2]), dv=atof(argv[3]);
  int Y=y*y; double Ly=log((double)y);
  int *spf=calloc(Y+1,sizeof(int));
  for(int i=2;i<=Y;i++) if(!spf[i]) for(long j=i;j<=Y;j+=i) if(!spf[j]) spf[j]=i;
  double **lam=calloc(Y+1,sizeof(double*)); double **al=calloc(Y+1,sizeof(double*));
  FILE*f=fopen("taup.txt","r"); long p; double t; int np=0;
  while(fscanf(f,"%ld %lf",&p,&t)==2){ if(p>Y) break; np++;
    double l=t/pow((double)p,5.5); double *L=calloc(J+EMAX+2,sizeof(double));
    L[0]=1; L[1]=l; for(int j=2;j<J+EMAX+2;j++) L[j]=l*L[j-1]-L[j-2]; lam[p]=L;
    double P[EMAX+1]={0}; P[0]=1;P[1]=-l;P[2]=1; double *A=calloc(EMAX+1,sizeof(double)); A[0]=1;
    for(int k=1;k<=EMAX;k++){double s=P[k]; for(int i=1;i<k;i++) s-=A[i]*A[k-i]; A[k]=s/2;} al[p]=A; }
  fclose(f);
  for(int q=2;q<=Y;q++) if(spf[q]==q && !lam[q]){fprintf(stderr,"missing tau(%d)\n",q);return 1;}
  double *beta=calloc(y+1,sizeof(double));
  for(int n=1;n<=y;n++){ double a=1; int m=n; while(m>1){int pp=spf[m],e=0; while(m%pp==0){m/=pp;e++;} a*=al[pp][e];}
    beta[n]=a*(1-log((double)n)/Ly); }
  /* real rho at s=1 */
  double *rho1=calloc(Y+1,sizeof(double)); cplx *rhoS=calloc(Y+1,sizeof(cplx));
  double *lg=calloc(Y+1,sizeof(double)); for(int m=1;m<=Y;m++) lg[m]=log((double)m);
  cplx *x=calloc(Y+1,sizeof(cplx)), *eg=calloc(Y+1,sizeof(cplx)), *hh=calloc(Y+1,sizeof(cplx));
  cplx *rp=calloc((Y+1)*(size_t)EMAX,sizeof(cplx)); /* rho_p(k,s) table indexed p*EMAX+k */
  for(int pass=0; ; pass++){
    double v = pass==0 ? 0.0 : (pass-1)*dv;
    if(pass>0 && v>vmax+1e-12) break;
    cplx s = 1 - I*v;
    for(int q=2;q<=Y;q++) if(spf[q]==q){
      cplx X=cexp(-s*lg[q]); double *L=lam[q];
      cplx D=0,Xj=1; for(int j=0;j<J;j++){D+=L[j]*L[j]*Xj; Xj*=X;}
      int kmax=0; {long z=q; while(z<=Y){kmax++; z*=q;}}
      for(int k=1;k<=kmax && k<EMAX;k++){ cplx N=0; Xj=1; for(int j=0;j<J;j++){N+=L[j+k]*L[j]*Xj; Xj*=X;} rp[(size_t)q*EMAX+k]=N/D; }
    }
    for(int m=1;m<=Y;m++){ cplx r=1; int z=m; while(z>1){int pp=spf[z],e=0; while(z%pp==0){z/=pp;e++;} r*=rp[(size_t)pp*EMAX+e];} rhoS[m]=r; }
    if(pass==0){ for(int m=1;m<=Y;m++) rho1[m]=creal(rhoS[m]); continue; }
    for(int m=1;m<=Y;m++){ eg[m]=cexp(-I*v*lg[m]); hh[m]=cexp(-I*v*lg[m]/2); x[m]=0; }
    for(int a=1;a<=y;a++) if(beta[a]!=0) for(int c=1;c<=y;c++) x[a*c]+=beta[a]*beta[c]*conj(eg[a]); /* a^{iv} */
    cplx S=0,S0=0;
    for(int P=1;P<=Y;P++){ if(x[P]==0) continue; cplx xp=x[P]/P;
      for(int Q=P;Q<=Y;Q++){ if(x[Q]==0) continue;
        int g=gcd(P,Q); int P1=P/g,Q1=Q/g; cplx w = (Q==P?1.0:2.0)*xp*x[Q]/Q*g;
        S  += w*eg[g]*rhoS[P1]*rhoS[Q1];
        S0 += w*hh[P]*hh[Q]*conj(eg[g])*rho1[P1]*rho1[Q1]; } }
    /* symmetry check needs S(P,Q)=S(Q,P): true since x_v(Q) is the same function (b<->d relabel) */
    printf("%.6f %.12e %.12e %.12e %.12e\n",v,creal(S),cimag(S),creal(S0),cimag(S0)); fflush(stdout);
  }
  return 0;
}
