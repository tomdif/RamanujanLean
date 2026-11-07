# Andrews–Dragonette partial sums P_N(n) for FIXED n, N -> infinity (double precision, numpy).
# term_k = (-1)^{floor((k+1)/2)} A_{2k}(n - k(1+(-1)^k)/4) * MK(2k,n),
# MK(K,n) = sqrt48/(sqrtK sqrt(24n-1)) sinh(pi sqrt(24n-1)/(6K))  (= Andrews66.MK; MK_two)
# A_K(x) = sum_{h mod K, (h,K)=1} exp(pi i s(h,K) - 2 pi i x h/K)  (= Andrews66.AAnd)
import os, sys, math
os.environ.setdefault("OMP_NUM_THREADS","2")
import numpy as np
KMAX=int(sys.argv[1]) if len(sys.argv)>1 else 4000
NS=[1,2,3,5,10,20,50,100]
def alpha_exact(M):
    a=[0]*(M+1); n=0
    while n*n<=M:
        t=[0]*(M+1); t[n*n]=1
        for j in range(1,n+1):
            for _ in range(2):
                for i in range(j,M+1): t[i]-=t[i-j]
        for i in range(M+1): a[i]+=t[i]
        n+=1
    return a
al=alpha_exact(max(NS))
def ded(h,k):
    # Dedekind sum s(h,k), 0<=h<k, gcd 1, by reciprocity (float)
    s=0.0; sg=1.0
    while k>1:
        h%=k
        if h==0: break
        s+=sg*((h/k+k/h+1/(h*k))/12-0.25)
        h,k=k,h; sg=-sg
    return s
P={n:0.0 for n in NS}; S={n:0.0 for n in NS}   # S = sum c_k/k (Kloosterman partial sum)
absP={n:0.0 for n in NS}
rows=[]
checkpoints=set([10,20,50,100,200,500,1000,2000,4000,8000,16000])|{KMAX}
for k in range(1,KMAX+1):
    K=2*k
    hs=np.array([h for h in range(1,K,2) if math.gcd(h,K)==1],dtype=np.float64)
    ss=np.array([ded(int(h),K) for h in hs])
    sign=(-1)**((k+1)//2)
    for n in NS:
        m=n-(k*(1+(-1)**k))/4
        A=np.cos(np.pi*ss-2*np.pi*m*hs/K).sum()   # A is real
        c=sign*A
        r=math.sqrt(24*n-1)
        MK=math.sqrt(48)/(math.sqrt(K)*r)*math.sinh(math.pi*r/(6*K))
        P[n]+=c*MK; S[n]+=c/k; absP[n]+=abs(c*MK)
    if k in checkpoints:
        rows.append((k,{n:(P[n]-al[n],S[n],absP[n]) for n in NS}))
        print("N=%6d "%k+" ".join("n=%d:err=%+.4f S/sqrtN=%+.3f abs=%.1f"%(n,P[n]-al[n],S[n]/math.sqrt(k),absP[n]) for n in NS),flush=True)
