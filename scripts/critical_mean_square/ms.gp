default(nbthreads,1); default(realprecision,38);
mf=mfinit([1,12],1); F=mfbasis(mf)[1]; L=lfunmf(mf,F);
Tm=400; Li=lfuninit(L,[6,0,Tm+1]);
h=1/20; S=0.; c=0.384084054468170;
forstep(k=0,Tm/h,1, t=k*h; v=abs(lfun(Li,6+I*t))^2; w=if(k==0,1/2,1); S+=w*v*h; if(k>0 && (k%1000==0), print(t," ",S," ratio ",S/(2*c*t*log(t))," minus-main/T ", (S-2*c*t*log(t/(2*Pi*exp(1))))/t)));
