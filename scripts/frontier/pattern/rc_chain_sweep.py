# Sweep rc_tail_lattice.rec_test over the whole s=-1 chain: every even k, 1<=j<=k'-1.
import sys
src=open('rc_tail_lattice.py').read().split("if __name__=='__main__'")[0]
exec(src)
p=int(sys.argv[1]);kmin=int(sys.argv[2]) if len(sys.argv)>2 else 4
T=O=H=L=LB=NT=C=skipped=0;bad=[]
for k in range(kmin,p,2):
    kp=p+1-k
    for j in range(1,kp):
        a=k+2*j;PR=j+5;N=k+j+3
        while p**PR>=2**63:PR-=1
        if PR<j+1:
            print(p,'k',k,'j',j,'SKIP precision');skipped+=1;continue
        r=rec_test(p,a,-1,j,PR,N)
        if r is None:continue
        print(p,'k',k,'j',j,'w',a-p+1,r,flush=True)
        H+=r['hn']
        if not r['hn']:bad.append((k,j,'noHN'));continue
        T+=r.get('tot',0);O+=r.get('ok',0);NT+=r.get('nontriv',0);C+=r.get('ctl',0)
        if r.get('law') is True:L+=1
        if r.get('law') is False:LB+=1;bad.append((k,j,'law'))
        for x in('rowsbad','tailbad','dbad','cbad','bbad','abad'):
            if r[x]:bad.append((k,j,x,r[x]))
        if r.get('fails'):bad.append((k,j,'rec',r['fails']))
print('SUMMARY p',p,'vertices ok',H,'recursion',O,'/',T,'nontrivial',NT,'wrong-constant passes',C,'law ok',L,'law bad',LB,'skipped',skipped,'problems',bad[:12],flush=True)
