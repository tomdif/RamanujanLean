default(nbthreads,1);
{forprime(l=13,41,
 k=l-3; mf=mfinit([6,k],0); B=mfeigenbasis(mf);
 for(i=1,#B, f=B[i]; v=mfcoefs(f,l);
   a2=v[3]; a3=v[4];
   if(a2==kronecker(2,l)*2^((l-5)/2)&&a3==kronecker(3,l)*3^((l-5)/2),
     cp=if(type(v[l+1])=="t_POLMOD",minpoly(v[l+1]),x-v[l+1]); print(l," a_l minpoly ",cp," eps ",kronecker(3,l)));
 ));}
