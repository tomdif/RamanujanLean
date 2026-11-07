# Compare Smith multiplicities of T_l on M_w(1) (integral Miller basis), Newton slopes, and Katz blocks dim M_{a+t(l-1)}-dim M_{a+(t-1)(l-1)}
import sys,subprocess,re
exec(open('rc_quotient_test.py').read().rsplit("if __name__=='__main__'",1)[0])
def snf_vals(M,p):
    src="default(parisize,1000000000);\n"+"M=["+";".join(",".join(str(x) for x in r) for r in M)+"];\nprint(matsnf(M));\nprint(Vec(charpoly(M)));\nquit;\n"
    o=subprocess.run(['gp','-q'],input=src,capture_output=True,text=True).stdout
    L=[x for x in o.splitlines() if x.startswith('[')]
    d=[int(t) for t in re.findall(r'-?\d+',L[0])]
    c=[int(t) for t in re.findall(r'-?\d+',L[1])]
    return d,c
def v(x,p):
    if x==0:return 99
    t=0
    while x%p==0:x//=p;t+=1
    return t
def hist(vals):
    h={}
    for x in vals:h[x]=h.get(x,0)+1
    return h
def newton(c,p):
    n=len(c)-1;pts=[(i,v(c[i],p)) for i in range(n+1) if c[i]]
    hull=[]
    for q in pts:
        while len(hull)>=2 and (hull[-1][1]-hull[-2][1])*(q[0]-hull[-1][0])>=(q[1]-hull[-1][1])*(hull[-1][0]-hull[-2][0]):hull.pop()
        hull.append(q)
    h={}
    for a,b in zip(hull,hull[1:]):
        h[round((b[1]-a[1])/(b[0]-a[0]),3)]=b[0]-a[0]
    return h
p=int(sys.argv[1]);smax=int(sys.argv[2]);agree=tot=0
for a in range(4,p+2,2):
  for s in range(1,smax+1):
    w=a+s*(p-1)
    T=heckemat(p,w)
    d,c=snf_vals(T,p)
    S=hist([v(x,p) for x in d if x]);N=newton(c,p)
    B={t:dimM(a+t*(p-1))-(dimM(a+(t-1)*(p-1)) if t else 0) for t in range(s+1)}
    B={t:x for t,x in B.items() if x}
    same=(S=={int(k):x for k,x in N.items() if k==int(k)} and all(k==int(k) for k in N))
    tot+=1;agree+=same
    print(f'a={a} s={s} w={w} Smith={S} Newton={N} blocks={B} {"S=N" if same else "S!=N"}',flush=True)
print('Smith=Newton',agree,'/',tot)
