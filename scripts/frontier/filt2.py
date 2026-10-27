import sys
exec(open('filt.py').read().split("mod=l**3")[0])
kmax=int(sys.argv[2]); bmax=int(sys.argv[3])
mod=l**(kmax+1)
Lf={}
for b in range(1,bmax+3):
    f=Lform(b,L,mod)
    if f is None: break
    Lf[b]=f
for b in range(1,bmax+1):
    if b+2 not in Lf: break
    for k in range(1,min(b,kmax)+1):
        A,B=Lf[b+2],Lf[b]
        # K mod l^(k+1) from leading coefficient (q^1)
        K=A[1]*pow(B[1],-1,l**(k+1))%(l**(k+1))
        diff=[(x-K*y)%(l**(k+1)) for x,y in zip(A,B)]
        ok=all(x%(l**k)==0 for x in diff)
        eps=[(x//l**k)%l for x in diff]
        allzero=all(x==0 for x in eps[:200])
        w=None if allzero else filtration(eps,l**k*(l-1))
        print(f'l={l} b={b} k={k}: prop mod l^k {ok}; eps=(L(b+2)-K L(b))/l^k mod l: ' + ('ZERO (prop mod l^(k+1))' if allzero else f'filtration {w}'),flush=True)
