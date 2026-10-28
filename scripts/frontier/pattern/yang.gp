\\ for prime l: charpoly mod l of T_l on S_{l-3}^{new}(6) split by AL signs (w2,w3)
f(l)={my(mf=mfinit([6,l-3],0),B=mfeigenbasis(mf),res=Map());
 for(i=1,#B, my(F=B[i], w2=mfatkineigenvalues(mf,2)[i][1], w3=mfatkineigenvalues(mf,3)[i][1], a=mfcoef(F,l), P);
   my(K=mffields(mf)[i]); P = if(poldegree(K)>1, charpoly(Mod(liftpol(a),K)), 'x-a);
   my(key=[w2,w3], old); old = if(mapisdefined(res,key), mapget(res,key), 1); mapput(res,key,old*P));
 print("l=",l," l%24=",l%24);
 my(M=Mat(res)); for(k=1,#M~, print("  (w2,w3)=",M[k,1],"  T_l charpoly mod l: ",factormod(M[k,2],l)));}
f(59); f(83);
mf3=mfinit([3,6],0); print(mfcoefs(mfeigenbasis(mf3)[1],5)); print(mfatkineigenvalues(mf3,3));
