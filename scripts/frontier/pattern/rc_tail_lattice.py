# Tests the tail-weighted lattice repair of the recursion (BL_SHARPNESS_PROOF section 4.10).
# L(a,j,k): coefficients c_r of x_r = b_r E^{s-r} with v(c_r) >= (l/(l+1)) max(r-J,0), J=k+j-2, a=k+2j.
# (T1) Katz coefficients of R = (P-lVP)/(l-1) in class 2 satisfy v(rho_t) >= (l/(l+1))(t-1).
# (T2) block valuations on the actual matrix of U, including tails.
# (T3) Schur complement R_j = D'-C'A'^{-1}B' mod l: rows > j vanish, tail columns vanish.
# (T4) R_j[theta z] = c_j [theta R_{j-1} z] on all of Fil^{J-1}(K), not only on Fil^{j-1}(K).
# (T5) charpoly of R_j on gr^j = law u*T|S_k * u*T^-1|M_{l+1-k} (level 1, s>=1 or s<0).
import sys,sympy
from fractions import Fraction
from flint import nmod_poly,nmod_mat
src=open('rc_tri_test.py').read()
exec(src.split("def cbin")[0].split("class R:")[0])
exec("class R:"+src.split("class R:")[1].split("def cbin")[0])
class K:
    def __init__(S,p,a,PR,N):
        S.p,S.a,S.PR,S.N=p,a,PR,N;S.m=m=p**PR
        S.dims=[dimM(a+i*(p-1)) for i in range(N+1)];S.dN=S.dims[N]
        S.idx=[next(i for i in range(N+1) if S.dims[i]>t) for t in range(S.dN)]
        S.LQ=S.dN+2;S.Lq=p*S.LQ+2;S.A=A=R(p,PR,S.Lq)
        S.E4=A.eis(4);S.E6=A.eis(6);S.E=A.eis(p-1)
        S.Dl=A.tr((A.pw(S.E4,3)-A.mul(S.E6,S.E6))*pow(1728,-1,m))
        S.Ei=S.inv(S.E)
        S.M={i:S.miller(a+i*(p-1)) for i in range(N+1)}
        S.EM={i:[A.mul(f,S.E) for f in S.M[i-1]] for i in range(1,N+1)}
        S.EN=A.pw(S.E,N)
    def inv(S,f):
        A=S.A;m=S.m;g=A.P([pow(int(f[0]),-1,m)]);n=1
        while n<S.Lq:
            n=min(2*n,S.Lq);fg=nmod_poly(((f*g)).coeffs()[:n],m);g=nmod_poly((g*(A.P([2])-fg)).coeffs()[:n],m)
        return g
    def miller(S,kk):
        A=S.A;d=dimM(kk);out=[]
        for x in range(d):
            r=kk-12*x
            for c in range(3):
                if r-6*c>=0 and (r-6*c)%4==0:b=(r-6*c)//4;break
            out.append(A.mul(A.mul(A.pw(S.Dl,x),A.pw(S.E4,b)),A.pw(S.E6,c)))
        for t in range(d-1,-1,-1):
            for u in range(t):
                c=int(out[u][t]) if t<out[u].length() else 0
                if c:out[u]=out[u]-out[t]*c
        return out
    def Epow(S,n):
        return S.A.pw(S.E,n) if n>=0 else S.A.pw(S.Ei,-n)
    def decompose(S,F):
        A=S.A;m=S.m;LQ=S.LQ;N=S.N
        G=nmod_poly(A.mul(F,S.EN).coeffs()[:LQ],m);out=[0]*S.dN
        for i in range(N,0,-1):
            R_=G;c=[]
            for t in range(len(S.EM[i])):
                ct=int(R_[t]) if t<R_.length() else 0;c.append(ct)
                if ct:R_=R_-nmod_poly(S.EM[i][t].coeffs()[:LQ],m)*ct
            for t in range(S.dims[i-1],S.dims[i]):
                out[t]=int(R_[t]) if t<R_.length() else 0
            G=A.P([0])
            for t,x in enumerate(c):
                if x:G=G+nmod_poly(S.M[i-1][t].coeffs()[:LQ],m)*x
        for t in range(S.dims[0]):
            out[t]=int(G[t]) if t<G.length() else 0
        return out
    def Umat(S,s):
        A=S.A;Es_inv=S.Epow(-s);cols=[]
        for col in range(S.dN):
            x=A.mul(S.M[S.idx[col]][col],S.Epow(s-S.idx[col]))
            cols.append(S.decompose(A.tr(A.U(x)*Es_inv)))
        return [[cols[c][r] for c in range(S.dN)] for r in range(S.dN)]
    def basis_modp(S,i):
        "reductions of b_t of index <= i, as lists mod p"
        p=S.p;n=S.dims[i];B=[]
        for t in range(n):
            f=S.M[S.idx[t]][t];B.append(f)
        return B
def val(x,p,PR):
    x%=p**PR
    if x==0:return PR
    c=0
    while x%p==0:x//=p;c+=1
    return c
def T1(p,PR,N):
    S=K(p,2,PR,N);A=S.A;m=S.m;L=S.Lq
    sg=[0]*L
    for d in range(1,L):
        for n in range(d,L,d):sg[n]=(sg[n]+d)%m
    i12=pow(12,-1,m);i1=pow(p-1,-1,m)
    Pc=[i12]+[(-2*sg[n])%m for n in range(1,L)]
    Rc=[Pc[n] for n in range(L)]
    for n in range(0,(L+p-1)//p):Rc[p*n]=(Rc[p*n]-p*Pc[n])%m
    Rq=A.P([x*i1%m for x in Rc])
    co=S.decompose(Rq);bad=[];rows={}
    for t,c in enumerate(co):
        i=S.idx[t];v=val(c,p,PR);rows[i]=min(rows.get(i,PR),v)
        if v<PR-1 and v<Fraction(p*(i-1),p+1):bad.append((i,t,v))
    print(f'T1 p={p}: min v(rho_t) by index',sorted(rows.items()),'violations',bad[:8],flush=True)
    return not bad
def blocks(S,U,j,k):
    "Schur complement R_j on high coords; returns dict"
    p=S.p;PR=S.PR;J=k+j-2;idx=S.idx;n=S.dN
    lam=lambda r:Fraction(p*max(r-J,0),p+1)
    low=[t for t in range(n) if idx[t]<j];high=[t for t in range(n) if idx[t]>=j]
    info=dict(rowsbad=0,tailbad=0,dbad=0,cbad=0,bbad=0,abad=0)
    # valuations are conclusive only below PR; PR is chosen above the tested scale
    for t in high:
        for r in range(n):
            v=val(U[t][r],p,PR)
            if v>=PR:continue
            sc=v+lam(idx[r])-lam(idx[t])
            if sc<j:info['dbad' if idx[r]>=j else 'cbad']+=1
            if idx[t]>j and sc<=j:info['rowsbad']+=1
            if idx[r]>J and sc<=j:info['tailbad']+=1
    for t in low:
        for r in range(n):
            v=val(U[t][r],p,PR)
            if v>=PR:continue
            sc=v+lam(idx[r])
            if idx[r]<=J and v<idx[t]:info['abad' if idx[r]<j else 'bbad']+=1
            if idx[r]>J and sc<=idx[t]:info['tailbad']+=1
    d=lambda t,e:(U[t[0]][t[1]]%p**PR)//p**e%p
    if not low:
        Rm={t:{r:d((t,r),j) for r in high if idx[r]<=J} for t in high if idx[t]==j}
        info['det']=True;info['R']=Rm;info['high']=[r for r in high if idx[r]<=J];return info
    Ap=nmod_mat(len(low),len(low),[d((t,r),idx[t]) for t in low for r in low],p)
    try:
        Ai=Ap.inv();info['det']=True
    except Exception:
        info['det']=False;return info
    cols=[r for r in high if idx[r]<=J];rws=[t for t in high if idx[t]==j]
    Bp=nmod_mat(len(low),len(cols),[d((t,r),idx[t]) for t in low for r in cols],p)
    Cp=nmod_mat(len(rws),len(low),[d((t,r),j) for t in rws for r in low],p)
    Dp=nmod_mat(len(rws),len(cols),[d((t,r),j) for t in rws for r in cols],p)
    Sc=Dp-Cp*Ai*Bp
    info['R']={t:{r:int(Sc[a,b]) for b,r in enumerate(cols)} for a,t in enumerate(rws)}
    info['high']=cols
    return info
def thetaP(f,p,n):
    return [i*int(f[i])%p if i<f.length() else 0 for i in range(n)]
def coords(f,bas,idxmax,p):
    "greedy q-order coordinates in Miller echelon basis; returns coords, leftover"
    f=[x%p for x in f];out={}
    for t,b in enumerate(bas):
        c=f[t]
        if c:
            for i in range(len(f)):
                if i<b.length():f[i]=(f[i]-c*int(b[i]))%p
            out[t]=c
    return out,any(f)
src2=open('rc_slope_law_level1.py').read().split("tot=ok=0")[0]
def law(p,k,s,j):
    "predicted monic charpoly high->low of R_j on gr^j"
    ns={'sys':sys}
    saved=sys.argv
    exec(src2,ns)
    cp=ns['cp']
    u=Fraction(1)
    for i in range(j):u*=Fraction(s-i,k+i)
    if u.numerator%p==0 or u.denominator%p==0:return None
    uu=u.numerator*pow(u.denominator,-1,p)%p
    sc=lambda T,x:[pow(x,i,p)*T[i]%p for i in range(len(T))]
    def rev(T):
        if len(T)==1:return T
        r=T[::-1];iv=pow(r[0],-1,p);return [y*iv%p for y in r]
    def mul(A,B):
        o=[0]*(len(A)+len(B)-1)
        for i,x in enumerate(A):
            for t,y in enumerate(B):o[i+t]=(o[i+t]+x*y)%p
        return o
    Tk=[x%p for x in cp(p,k)] if k>=12 else [1]
    kp=p+1-k
    if kp<0:return None
    hp=[x%p for x in cp(p,kp)] if kp>=12 else [1]
    if kp>=4:hp=mul(hp,[1,p-1])
    if hp[-1]==0:return None
    return mul(sc(Tk,uu),sc(rev(hp),uu))
def grcharpoly(info,S,j,p):
    rows=sorted(info['R']);n=len(rows)
    if n==0:return [1]
    M=nmod_mat(n,n,[info['R'][t].get(r,0) for t in rows for r in rows],p)
    co=[int(x) for x in M.charpoly().coeffs()]
    return co[::-1]
def strip(c):
    c=c[:]
    while len(c)>1 and c[-1]==0:c.pop()
    return c
def rec_test(p,a,s,j,PR,N):
    k=a-2*j
    if k<3:return None
    Sw=K(p,a,PR,N);Uw=Sw.Umat(s)
    SK=K(p,a-2,PR,N);UK=SK.Umat(s)
    iw=blocks(Sw,Uw,j,k);iK=blocks(SK,UK,j-1,k)
    bad={x:iw[x]+iK[x] for x in ('rowsbad','tailbad','dbad','cbad','bbad','abad')}
    if not (iw['det'] and iK['det']):return dict(hn=False,**bad)
    J=k+j-2;JK=J-1;c=Fraction(s-j+1,k+j-1)
    lw=law(p,k,s,j) if k<=p+1 else None
    gc=strip(grcharpoly(iw,Sw,j,p))
    bad['law']=(None if lw is None else lw==gc)
    if (k+j-1)%p==0:return dict(hn=True,crit=True,**bad)
    cj=c.numerator*pow(c.denominator,-1,p)%p
    n=min(Sw.dims[min(J,N)]+6,Sw.LQ)
    ok=tot=nt=ctl=0;fails=[]
    bw=[Sw.M[Sw.idx[t]][t] for t in range(Sw.dims[min(J,N)])]
    bK=[SK.M[SK.idx[t]][t] for t in range(SK.dims[min(JK,N)])]
    def proj_w(vec):
        "vec: coords dict in w index <=J -> apply R_j: returns dict row->val"
        o={t:0 for t in iw['R']}
        for t in o:
            for r,x in vec.items():
                if r in iw['R'][t]:o[t]=(o[t]+iw['R'][t][r]*x)%p
        return o
    for t0 in range(len(bK)):
        if SK.idx[t0]<j-1:continue
        z=bK[t0]
        tz,lo=coords(thetaP(z,p,n),bw,J,p)
        if lo:fails.append(('thetaz out of Fil^J',t0));continue
        lhs=proj_w(tz)
        # z' = R_{j-1} z in gr^{j-1}(K) coordinates
        zp={r:iK['R'][r].get(t0,0) for r in iK['R']}
        g=[0]*n
        for r,x in zp.items():
            if x:
                b=SK.M[SK.idx[r]][r]
                for i in range(n):
                    if i<b.length():g[i]=(g[i]+x*int(b[i]))%p
        tg=[i*g[i]%p for i in range(n)]
        tgc,lo2=coords(tg,bw,J,p)
        if lo2:fails.append(('thetaz prime out',t0));continue
        rhs={t:cj*tgc.get(t,0)%p for t in iw['R']}
        rhsb={t:(cj+1)*tgc.get(t,0)%p for t in iw['R']}
        tot+=1
        same=all(lhs[t]==rhs[t] for t in lhs);ok+=same
        if any(rhs.values()):
            nt+=1;ctl+=all(lhs[t]==rhsb[t] for t in lhs)
        if not same:fails.append((t0,Sw.idx[t0] if t0<Sw.dN else None))
    return dict(hn=True,tot=tot,ok=ok,nontriv=nt,ctl=ctl,fails=fails[:4],**bad)
if __name__=='__main__':
    p=int(sys.argv[1]);PR=int(sys.argv[2]);N=int(sys.argv[3])
    if sys.argv[4]=='T1':
        T1(p,PR,N);sys.exit()
    for spec in sys.argv[4].split(','):
        a,s,j=map(int,spec.split(':'))
        print(f'p={p} a={a} s={s} j={j} k={a-2*j}',rec_test(p,a,s,j,PR,N),flush=True)
