import numpy as np
N=4000
M=1<<8
s1=np.zeros(N+1,dtype=np.int64)
for d in range(1,N+1): s1[d::d]+=d
s1%=M
ts1=(np.arange(N+1)*s1)%M
def mul(a,b):
    r=np.zeros(N+1,dtype=np.int64)
    for i in np.nonzero(a)[0]:
        r[i:]+= a[i]*b[:N+1-i]; r%=M
    return r
X=mul(s1,ts1); A=mul(X,X)
def PA(n,d): return (-17418240*n**3*d+104509440*n**4*d-125411328*n**5*d+17418240*n**2*d**3-139345920*n**3*d**3+194088960*n**4*d**3+34836480*n**2*d**5-78382080*n**3*d**5+9676800*n**2*d**7)
res={}
for n in range(1,N+1,2):
    g=sum(PA(n,d)+27648*d**11 for d in range(1,n+1) if n%d==0)
    assert g%2**18==0
    t=(g>>18)%8
    res.setdefault(n%8,[]).append((n,int(A[n]%4),t))
for r in [1,3,5,7]:
    print(r,res[r][:25])
    print(r, set((a,b) for _,a,b in res[r]))
