import numpy as np
p=np.fromfile('p1e8.bin',dtype=np.uint64); NMAX=len(p)-1
def v(x,l):
    if x==0: return 99
    c=0
    while x%l==0: x//=l; c+=1
    return c
for l,kmax in ((17,5),(19,4),(23,4)):
    Mod=l**kmax
    for a in range(1,6):
        A=l**(a+2); B=l**a; pairs=[]; N=1
        while True:
            if (B*N+1)%24==0:
                na=(A*N+1)//24; nb=(B*N+1)//24
                if na>NMAX: break
                pairs.append((int(p[na])%Mod,int(p[nb])%Mod))
            N+=1
        if len(pairs)<3: continue
        piv=[(x,y) for x,y in pairs if y%l]
        x0,y0=piv[0]
        beta=min(min(v((x*y0-x0*y)%Mod,l),kmax) for x,y in pairs)
        K=(x0*pow(y0,-1,Mod))%Mod
        print(f'l={l} alpha={a} tests={len(pairs)} proportional mod l^{beta}   K mod l^{min(beta,kmax)} = {K % l**min(beta,kmax)}')
