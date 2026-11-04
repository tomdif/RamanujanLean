exec(open('cv_proto.py').read().split('# ---- region (a)')[0])
def mkcells(lo,hi,n):
    lo=mp.mpf(lo); hi=mp.mpf(hi); return [(lo+(hi-lo)*i/n, lo+(hi-lo)*(i+1)/n) for i in range(n)]
exec(open('cv_proto.py').read().split('# ---- region (b)')[1].split('for u0 in')[0])
def regionB6(u0,nM,ncell):
    M=hullPhi(12,u0,nM); f=mp.factorial
    c0,c2,c4,c6,c8,c10=[c[2*j] for j in range(6)]
    bad=0; mn=mp.inf
    for (a,b) in mkcells(0,u0,ncell):
        U=iv.mpf([a,b])
        Ph=c0+c2*U**2/2+c4*U**4/24+c6*U**6/720+c8*U**8/f(8)+c10*U**10/f(10)+M*U**12/f(12)
        W=-2*c4/6-4*c6*U**2/f(5)-6*c8*U**4/f(7)-8*c10*U**6/f(9) + M*U**8/f(11) - M*U**8/f(10)
        V=c2+c4*U**2/6+c6*U**4/f(5)+c8*U**6/f(7)+c10*U**8/f(9)+M*U**10/f(11)
        g=Ph*W+V*V; mn=min(mn,g.a)
        if not g.a>0: bad+=1
    return M,bad,mn
KM=7
c=[PhiIv(i,iv.mpf(0)) for i in range(13)]
import sys
for u0 in ['0.16','0.18','0.2']:
    for nM in [100,200,400]:
        M,bad,mn=regionB(mp.mpf(u0),nM,40); print('N5',u0,nM,mp.nstr(M.b,4),bad,mp.nstr(mn,4)); sys.stdout.flush()
        M,bad,mn=regionB6(mp.mpf(u0),nM,40); print('N6',u0,nM,mp.nstr(M.b,4),bad,mp.nstr(mn,4)); sys.stdout.flush()
