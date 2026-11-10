import sys
sys.argv=[sys.argv[0],'120']
exec(open(__file__.replace('deg3.py','cramer.py')).read().split("g, h = G(), H()")[0])
def p(k): return Ng(chim(k))
def m(k): return chim(k)
for (i,j) in ((1,3),(1,7),(3,21),(1,21),(7,21),(3,7)):
    u=mul(p(i),p(j)); v=mul(m(i),m(j)); w=mul(u,v)
    d=add(u,sc(-1,v))
    print((i,j),'u-v:',d[:12])
    print('   (u-v)w:',mul(d,w)[:12])
    d2=add(mul(p(i),m(j)),sc(-1,mul(m(i),p(j))))
    print('   p_i m_j - m_i p_j:',d2[:12])
