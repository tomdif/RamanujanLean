exec(open('dtest.py').read().split("for c in (1,2):")[0])
E4=[1]+[240*sigma(n,3) for n in range(1,LL)]
G0=mul(Dq,[x%mod for x in E4],mod,LL)            # weight 16
G1=mul(G0,[x%mod for x in E4],mod,LL); G1=mul(G1,[x%mod for x in E4],mod,LL); G1=mul(G1,[x%mod for x in E4],mod,LL)  # weight 28? fix
print('check weight bookkeeping skipped')
f=G0
Uf=U(f)
print('U(Delta E4) digit filts', digitfilts(Uf,3,0))
print('Delta E4 digit filts', digitfilts(f[:L],3,0))
