default(parisize,1000000000);
{foreach([[29,1,1],[31,-1,1],[37,1,-1],[41,-1,1],[43,1,1],[47,-1,-1]],c,my(l=c[1],k=l-5,mf=mfinit([6,k],0),F=mfeigenbasis(mf),a2=mfatkineigenvalues(mf,2),a3=mfatkineigenvalues(mf,3));
 for(i=1,#F,if(a2[i][1]==c[2]&&a3[i][1]==c[3],print("[",l,",",lift(Mod(1,l)*mfcoefs(F[i],60)),"]"))));}
quit;
