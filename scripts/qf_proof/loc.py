import math
K=12
rows=[l.split() for l in open('taup.txt')]
out=[]
for ps,ts in rows:
    p=int(ps); X=1/p; l=int(ts)/p**5.5
    lam=[1,l]
    for j in range(2,3*K): lam.append(l*lam[-1]-lam[-2])
    LM=lambda j: 0 if j<0 else lam[j]
    P=[1,-l,1]+[0]*K; al=[1]+[0]*K
    for k in range(1,K+1): al[k]=(P[k]-sum(al[i]*al[k-i] for i in range(1,k)))/2
    D=[lam[j]**2 for j in range(K+1)]; s=[1]+[0]*K
    for k in range(1,K+1): s[k]=(D[k]-sum(s[i]*s[k-i] for i in range(1,k)))/2
    Fi=[s[k]*X**k for k in range(K+1)]
    def L(a,e):
        if a<e: return 0
        if e==0: return 1 if a==0 else X**a*(LM(a)-X*LM(a-2))/(1+X)
        return X**(a-e)*LM(a-e)
    def mass(e):
        G=[[al[i]*al[j]*L(i+j,e) for j in range(K)] for i in range(K)]
        m=0
        for i in range(K):
            for j in range(K):
                m+=abs(sum(G[a][b]*Fi[i-a]*Fi[j-b] for a in range(i+1) for b in range(j+1)))
        return m
    m0=mass(0); m1=mass(1); W1=X*((1+X)**2-X*l*l)/(1+X)**2
    f1=p*W1*m1*m1
    out.append((p,l,(m0-1)*p*p,(f1-l*l)*p,max(mass(e) for e in (2,3,4))))
import statistics
for r in out[:6]+out[100:103]+out[-3:]: print("p=%d lam=%.3f (m0-1)p^2=%.3f (f(p)-lam^2)p=%.3f max m_e(e=2..4)=%.3f"%r)
print('max |(m0-1)p^2|',max(abs(r[2]) for r in out),'max (f-lam^2)p',max(r[3] for r in out),'max m_e',max(r[4] for r in out))
