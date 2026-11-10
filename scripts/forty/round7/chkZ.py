from ser import *
def J(e,N): return T(N,e)
def Pinf(b,a):
    o=[0]*P;o[0]=1
    k=b
    while k<P:
        o=[o[i]-(o[i-k] if i>=k else 0) for i in range(P)]
        k+=a
    return o
def M(*xs):
    r=xs[0]
    for x in xs[1:]: r=mul(r,x)
    return r
print(M(J(4,32),J(16,32),J(12,32),J(16,32),Pinf(2,4))==M(J(2,16),J(6,16),Pinf(16,16),J(4,16)))
