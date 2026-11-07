default(parisize,1500000000);
cppred(l)={my(k=l-5,mf=mfinit([6,k],0),F=mfeigenbasis(mf),s2=-kronecker(2,l),s3=-kronecker(3,l),a2=mfatkineigenvalues(mf,2),a3=mfatkineigenvalues(mf,3),P=Mod(1,l)*x^0,dim=0,c=Mod(kronecker(12,l),l)/5);
 for(i=1,#F,if(a2[i][1]==s2&&a3[i][1]==s3,
   my(q=mfparams(F[i])[4],v=mfcoefs(F[i],l)[l+1],cp);
   cp=if(type(v)=="t_POLMOD",charpoly(v),x-v);
   \\ charpoly of a_l over the field; denominators prime to l assumed
   dim+=poldegree(cp);P*=Mod(1,l)*cp));
 my(deg=poldegree(P),S=sum(j=0,deg,polcoef(P,j)*c^(deg-j)*x^j));
 print("l=",l," classdim=",dim," pred=",lift(factormod(S,l)));};
{forprime(l=29,113,cppred(l));}
my(n8=mfinit([6,8],0),G=mfeigenbasis(n8));print("wt8 new ",#G," w2 ",mfatkineigenvalues(n8,2)," w3 ",mfatkineigenvalues(n8,3));
for(i=1,#G,print(" a2 a3 a5 ",mfcoefs(G[i],5)[3..6]));
my(n6=mfinit([6,6],0),H=mfeigenbasis(n6));print("wt6 new ",#H," w2 ",mfatkineigenvalues(n6,2)," w3 ",mfatkineigenvalues(n6,3));
quit;
