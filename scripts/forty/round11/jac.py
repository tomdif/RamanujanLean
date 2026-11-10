import sys
sys.argv=[sys.argv[0],'200']
exec(open(__file__.replace('jac.py','cramer.py')).read().split("g, h = G(), H()")[0])
p=Ng(chim(1)); m=chim(1)
def pw(a,k):
    r=[1]+[0]*(N-1)
    for _ in range(k): r=mul(r,a)
    return r
lhs=mul(add(pw(p,8),sc(-1,pw(m,8))),pw(mul(p,m),8))
print('Jacobi:', [(i,x) for i,x in enumerate(lhs) if x][:4])
