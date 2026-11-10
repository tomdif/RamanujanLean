from ps import *
A=mul(mul(chi(1),chi(3,-1)),mul(chi(7),chi(21,-1)))
E=[A[2*i] if 2*i<N else 0 for i in range(N)]
O=[A[2*i+1] if 2*i+1<N else 0 for i in range(N)]
L1=add(mul(G(3),G(7)),mul(mono(2),mul(H(3),H(7))))
print("O==L1:", eq(O,L1,140))
print("E:",E[:30])
# try E as eta quotients: compute log-derivative style exponents: E = prod (1-q^n)^{a_n}
def etaexp(a,M=60):
    a=a[:]; ex=[]
    import copy
    cur=a
    exps={}
    for n in range(1,M):
        c=cur[n]
        exps[n]=-c
        # divide cur by (1-q^n)^{-c}  i.e multiply by (1-q^n)^{c}
        f=add(ONE,mono(n,-1))
        if c>0:
            for _ in range(c): cur=mul(cur,f)
        elif c<0:
            fi=inv(f)
            for _ in range(-c): cur=mul(cur,fi)
    return exps
print(etaexp(E,50))
print(etaexp(L1,50))
