# region (a) feasibility with crude tails: sigma_i = 2*A_i*(4x)^{n_i}/2^i,  t_i <= sigma_i e^{-4x}
import mpmath as mp
mp.mp.dps=30; pi=mp.pi
def step(l):
    n=len(l); r=[0]*(n+1)
    for d,c in enumerate(l):
        r[d]+=c; r[d+1]-=4*c
        if d>=1: r[d]+=4*d*c
    while r and r[-1]==0: r.pop()
    return r
Z=[[0,-3,2]]
for i in range(12): Z.append(step(Z[-1]))
print(Z[:3])
pe=lambda l,z: sum(c*z**d for d,c in enumerate(l))
A=[sum(abs(c) for c in l) for l in Z]; n=[len(l)-1 for l in Z]
def check(u):
    x=pi*mp.exp(2*u)
    p=[pe(Z[i],x)/2**i for i in range(3)]
    s=[2*A[i]*(4*x)**n[i]/2**i for i in range(3)]
    F=8*x**3*(2*u-1)+x**2*(42-48*u)+60*x*(u-1)+mp.mpf(45)/2
    lhs=x**2*F
    cr=mp.exp(-3*x)*(abs(p[0])*(s[1]+u*s[2])+s[0]*(abs(p[1])+u*abs(p[2]))+2*u*abs(p[1])*s[1])+mp.exp(-6*x)*(s[0]*(s[1]+u*s[2])+u*s[1]**2)
    return lhs, cr
for u in ['0.1','0.12','0.14','0.15','0.16','0.18','0.2','0.3','0.5','1','2','3']:
    l,c=check(mp.mpf(u)); print(u, mp.nstr(l,6), mp.nstr(c,6), mp.nstr(c/l,4))
# ratio condition for tail: ((k+2)/(k+1))^{2n} e^{-(2k+3)x} <= 1/2 for k>=1, x>=pi
for nn in [2,3,4,12]:
    print(nn, (mp.mpf(3)/2)**(2*nn)*mp.exp(-5*pi))
