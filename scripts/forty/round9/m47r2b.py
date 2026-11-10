import sys; from tree import *
# (R2): QS(12,2,16) - QS(16,4,48) - (1/2) t^12 * sum_{x,y mod 4 with T(x)=T(y) mod 2} QS(1,0,47,1,47)|coset
T=lambda n:(n*(n+1)//2)%2
terms=[(1,0,(12,2,16,0,0,0,0)),(-1,0,(16,4,48,0,0,0,0))]
for r1 in range(4):
    for r2 in range(4):
        if T(r1)==T(r2):
            k0,sg,G=sub((1,0,47,1,47,0,0),[[4,0],[0,4]],(r1,r2))
            terms.append((-0.5,12+k0,G))
tot=np.zeros(P,dtype=np.float64)
for c,k,F in terms: tot+=c*form(F,k)
print("R2 identity:",not np.abs(tot[:P-400]).max()>1e-9)
for D in (1,2,3):
    resid,*_=search(terms,D); print("depth",D,"residual",resid)
    if resid<1e-6: break
