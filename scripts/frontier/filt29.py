import sys
exec(open('filt.py').read().split("mod=l**3")[0])
mod=l**3
Lf={b:Lform(b,L,mod) for b in (1,2,3)}
A,B=Lf[3],Lf[1]
i0=next(i for i,x in enumerate(B) if x%l)
K=A[i0]*pow(B[i0],-1,l*l)%(l*l)
print("leading index",i0)
eps=[((x-K*y)%(l*l))//l for x,y in zip(A,B)]
print('l',l,'w(eps_11)=',filtration(eps,l*(l-1)))
# apply U then check whether eps|U mod l lies in the span of L(2) mod l (the stable line)
def U(f): return [f[l*n] for n in range(len(f)//l)]
eU=[x%l for x in U(eps)]
L2=[x%l for x in Lf[2]]
n=len(eU)
rk=rank_mod([L2[:n]],l); rk2=rank_mod([L2[:n],eU[:n]],l)
print('eps|U in line spanned by L(2) mod l?', rk2==rk, ' w(eps|U)=',filtration(eU+[0]*(L-len(eU)),l*(l-1)))
