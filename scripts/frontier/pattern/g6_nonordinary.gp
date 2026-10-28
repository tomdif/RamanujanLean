default(parisize,"2G");
mf=mfinit([6,6],0); B=mfeigenbasis(mf); print(#B);
F=B[1]; print(mfcoefs(F,10));
print(mfatkineigenvalues(mf,2)); print(mfatkineigenvalues(mf,3));
N=300000; c=mfcoefs(F,N);
forprime(p=5,N, if(c[p+1]%p==0, print("nonord ",p," a_p=",c[p+1])));
