#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#define KMAX 64
int Y,y; int *spf;
double lamp[KMAX+3], *LAM; // per prime storage
typedef struct { double lam[KMAX+3]; double al[KMAX+1]; double L[KMAX+1][KMAX+1]; double Ld[KMAX+1][KMAX+1]; double W[KMAX+1], Wd[KMAX+1]; } PD;
PD **pd;
int main(int argc,char**argv){
  y=atoi(argv[1]); Y=y*y; double Ly=log((double)y);
  spf=calloc(Y+1,sizeof(int));
  for(int i=2;i<=Y;i++) if(!spf[i]) for(long j=i;j<=Y;j+=i) if(!spf[j]) spf[j]=i;
  pd=calloc(y+1,sizeof(PD*));
  FILE*f=fopen("taup.txt","r"); long p; double t;
  while(fscanf(f,"%ld %lf",&p,&t)==2){ if(p>y) break;
    PD*q=calloc(1,sizeof(PD)); pd[p]=q; double X=1.0/p, l=t/pow((double)p,5.5);
    q->lam[0]=1; q->lam[1]=l; for(int j=2;j<=KMAX+2;j++) q->lam[j]=l*q->lam[j-1]-q->lam[j-2];
    #define LM(j) ((j)<0?0.0:q->lam[j])
    // alpha: sqrt(1 - l X + X^2)
    double P[KMAX+1]={0}; P[0]=1;P[1]=-l;P[2]=1; q->al[0]=1;
    for(int k=1;k<=KMAX;k++){double s=P[k]; for(int i=1;i<k;i++) s-=q->al[i]*q->al[k-i]; q->al[k]=s/2;}
    for(int a=0;a<=KMAX;a++) for(int e=0;e<=KMAX;e++){
      double Lv=0,Ldv=0;
      if(a>=e){ if(e==0){ double r = a==0?1.0:(LM(a)-X*LM(a-2))/(1+X);
                  double rp = a==0?0.0:-(LM(a)+LM(a-2))/((1+X)*(1+X));
                  Lv=pow(X,a)*r; double XdL = a*Lv + pow(X,a+1)*rp;
                  Ldv = 0.5*a*log((double)p)*Lv - log((double)p)*XdL; }
               else { Lv=pow(X,a-e)*LM(a-e); Ldv=0.5*a*log((double)p)*Lv - log((double)p)*(a-e)*Lv; } }
      q->L[a][e]=Lv; q->Ld[a][e]=Ldv; }
    double qq=(1+X)*(1+X)-X*l*l, qp=2*(1+X)-l*l;
    q->W[0]=1; q->Wd[0]=0;
    q->W[1]=X*qq/((1+X)*(1+X));
    { double d= qq/((1+X)*(1+X)) + X*qp/((1+X)*(1+X)) - 2*X*qq/pow(1+X,3); q->Wd[1]=-log((double)p)*X*d; }
    for(int e=2;e<=KMAX;e++){ double g=(1-X)*qq/(1+X); double gp=-qq/(1+X)+(1-X)*qp/(1+X)-(1-X)*qq/((1+X)*(1+X));
      q->W[e]=pow(X,e)*g; double d=e*pow(X,e-1)*g+pow(X,e)*gp; q->Wd[e]=-log((double)p)*X*d; }
  }
  // beta
  double *beta=calloc(y+1,sizeof(double));
  for(int n=1;n<=y;n++){ double a=1; int m=n; while(m>1){int pp=spf[m],e=0; while(m%pp==0){m/=pp;e++;} a*=pd[pp]->al[e];}
    beta[n]=a*(1-log((double)n)/Ly); }
  double *c=calloc(Y+1,sizeof(double));
  for(int a=1;a<=y;a++) if(beta[a]!=0) for(int b=1;b<=y;b++) c[a*b]+=beta[a]*beta[b];
  double *yd=calloc(Y+1,sizeof(double)), *zd=calloc(Y+1,sizeof(double));
  int pr[32],ex[32];
  for(int h=1;h<=Y;h++){ if(c[h]==0) continue; int m=h,k=0; while(m>1){int pp=spf[m],e=0; while(m%pp==0){m/=pp;e++;} pr[k]=pp;ex[k]=e;k++;}
    // enumerate divisors
    int ev[32]={0};
    while(1){ long d=1; double P=1,D=0;
      for(int i=0;i<k;i++){ PD*q=pd[pr[i]]; double Lv=q->L[ex[i]][ev[i]], Ldv=q->Ld[ex[i]][ev[i]]; D=D*Lv+P*Ldv; P*=Lv; for(int j=0;j<ev[i];j++) d*=pr[i]; }
      yd[d]+=c[h]*P; zd[d]+=c[h]*D;
      int i=0; while(i<k && ev[i]==ex[i]){ev[i]=0;i++;} if(i==k) break; ev[i]++; }
  }
  double Q0=0,Q1=0;
  for(int d=1;d<=Y;d++){ if(yd[d]==0&&zd[d]==0) continue; int m=d; double P=1,D=0;
    while(m>1){int pp=spf[m],e=0; while(m%pp==0){m/=pp;e++;} PD*q=pd[pp]; D=D*q->W[e]+P*q->Wd[e]; P*=q->W[e];}
    Q0+=P*yd[d]*yd[d]; Q1+=D*yd[d]*yd[d]+2*P*yd[d]*zd[d]; }
  printf("%d L=%.4f Q0=%.10f Q0*L=%.6f Q1'=%.6f\n",y,Ly,Q0,Q0*Ly,Q1);
  return 0;
}
