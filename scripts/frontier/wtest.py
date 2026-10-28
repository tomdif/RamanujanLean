import sys
p=int(sys.argv[1]); PR=int(sys.argv[2]); NM=int(sys.argv[3])
sys.argv=['x',str(p),str(PR),str(NM),'none']
exec(open('katz.py').read().split("mode=sys.argv[4]")[0])
s=(p+1)//2
# W = Phi/Delta^delta = eta(p^2 z)/eta(z)^{p^2} as q-series: E(q^{p^2}) / E(q)^{p^2}  (q-powers cancel)
Ep2=[1]+[0]*(L-1)
# E(q)^{p^2}
def pw(f,e):
    r=[1]+[0]*(L-1); b=f[:]
    while e:
        if e&1: r=mul(r,b,L)
        b=mul(b,b,L); e>>=1
    return r
Ep2=pw(eta,p*p)
W=mul(El2,inv(Ep2,L),L)
EsW=mul(pw(E,s),W,L)
F=mul(EsW,pw(E,NM),L)       # weight NM(p-1) approx classical
res=katz_coeffs(F,NM)
vals=[v(a,DMAX) for a in res]
print(f'p={p}: Katz valuations of E^s W, i=0..{NM}:',vals)
print('required ceil(i/(p+1)) :',[-(-i//(p+1)) for i in range(NM+1)])
