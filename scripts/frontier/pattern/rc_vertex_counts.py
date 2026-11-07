# Pure dimension identities behind the s=-1 chain, level 1 (BL_SHARPNESS_PROOF section 4.10).
# (D1) dim gr^{j-1}(a-2) == dim gr^j(a) for 2<=j<=k'-1, a=k+2j (theta is then an iso on the block).
# (D2) dim gr^{k'-1}(a) at weight w=k' equals dim S_k + dim M_{k'}.
# (D3) for w=a-(l-1)>2, 1<=j, the count and height of the classical+Bol slope list below j equal the
#      formal Hodge count dim Fil^{j-1}(a) and height sum_{t<j} t dim gr^t(a).
# (D4) for a<=l+1, gr^t(a) = dim S_{a-2t}+dim M_{l+1-a+2t} for 1<=t<=(a-4)/2, when a-2t>=4.
def dM(k):
    if k<0 or k%2 or k==2:return 0
    return k//12+(0 if k%12==2 else 1)
def dS(k):
    return max(dM(k)-1,0) if k>=4 or k==0 else 0
def dS0(k):return 0 if k==0 else dS(k)
def gr(a,t,l):
    return dM(a) if t==0 else dM(a+t*(l-1))-dM(a+(t-1)*(l-1))
def dimS_Gamma0(k,l):
    # dim S_k(Gamma0(l)), l>=5 prime, k>=2 even
    g=(l+1)//12 - (0 if l%12 in(1,) else 0)
    mu=l+1;e2=1+(-1 if l%4==3 else 1);e3=1+(-1 if l%3==2 else 1)
    from fractions import Fraction as F
    gg=1+F(mu,12)-F(e2,4)-F(e3,3)-1
    if k==2:return int(gg)
    return int((k-1)*(gg-1)+(F(k,2)-1)*2+e2*(k//4)+e3*(k//3))
def new(k,l):
    return dimS_Gamma0(k,l)-2*dS0(k)
fails={1:[],2:[],3:[],4:[]};cnt=[0]*5
from sympy import primerange
for l in primerange(13,400):
    for k in range(4,l+2,2):
        kp=l+1-k
        for j in range(2,kp):
            a=k+2*j;cnt[1]+=1
            if gr(a-2,j-1,l)!=gr(a,j,l):fails[1].append((l,k,j,gr(a-2,j-1,l),gr(a,j,l)))
        if kp>=2:
            a=k+2*(kp-1);cnt[2]+=1
            if gr(a,kp-1,l)!=dS(k)+dM(kp):fails[2].append((l,k,gr(a,kp-1,l),dS(k),dM(kp)))
        for j in range(1,kp):
            a=k+2*j;w=a-(l-1)
            if w<=2:continue
            cnt[3]+=1
            D=dM(a+(j-1)*(l-1));H=sum(t*gr(a,t,l) for t in range(j))
            # classical + Bol list below slope j
            c=dM(w);h=0
            n=new(w,l);c+=n;h2=(w-2)*n  # height doubled
            if j-1>=w-1:
                c+=dS(w);h2+=2*(w-1)*dS(w)
                a2=l+1-w;jj=j-w+1
                for t in range(jj):
                    g=gr(a2,t,l);c+=g;h2+=2*(t+w-1)*g
            if (c,h2)!=(D,2*H):fails[3].append((l,k,j,w,c,D,h2,2*H))
    for a in range(4,l+2,2):
        for t in range(1,(a-4)//2+1):
            cnt[4]+=1
            if gr(a,t,l)!=dS(a-2*t)+dM(l+1-a+2*t):fails[4].append((l,a,t))
for i in fails:print('D%d cases %d fails %d'%(i,cnt[i],len(fails[i])),fails[i][:8])
