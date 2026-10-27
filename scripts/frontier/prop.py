import numpy as np, sys
data={13:(np.fromfile('p_13.bin',dtype=np.int64),13**6)}
p2=np.fromfile('p_171923.bin',dtype=np.int64)
for l,k in ((17,5),(19,4),(23,4)): data[l]=(p2,None,k)
data[13]=(data[13][0],None,6)
NMAX=len(p2)-1
def v(x,l):
    if x==0: return 99
    c=0
    while x%l==0: x//=l; c+=1
    return c
for l,(p,_,kmax) in data.items():
    Mod=l**kmax
    for a in range(1,5):
        A=l**(a+2); B=l**a
        pairs=[]
        N=1
        while True:
            if (B*N+1)%24==0:
                na=(A*N+1)//24; nb=(B*N+1)//24
                if na>NMAX: break
                pairs.append((int(p[na])%Mod,int(p[nb])%Mod))
            N+=1
        if len(pairs)<5: continue
        # max beta s.t. a_i b_j - a_j b_i ≡ 0 mod l^beta for all i,j (use pivot with unit b)
        piv=[(x,y) for x,y in pairs if y%l]
        if not piv: print(l,a,'no unit b'); continue
        x0,y0=piv[0]
        beta=min(min(v((x*y0-x0*y)%Mod,l),kmax) for x,y in pairs)
        K=(x0*pow(y0,-1,l**max(beta,1)))%(l**max(beta,1))
        print(f'l={l} alpha={a} tests={len(pairs)} proportional mod l^{beta}  K mod l^beta = {K}')
