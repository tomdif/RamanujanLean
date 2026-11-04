from mpmath import mp, mpc, exp, pi, sqrt, nprod
mp.dps=30
I=mpc(0,1)
def eta(z):
    q=exp(2*pi*I*z)
    p=mpc(1); n=1
    while True:
        t=q**n
        p*= (1-t); n+=1
        if abs(t)<mp.mpf(10)**-32: break
    return exp(2*pi*I*z/24)*p
def leg(a,p):
    a%=p
    if a==0: return 0
    return 1 if pow(a,(p-1)//2,p)==1 else -1
def e24(n): return exp(2*pi*I*n/24)
def run(Q,k=12):
    G=lambda z: eta(z)**24
    F=lambda z: G(z)/eta(z)
    cM=mp.mpf(Q)**(k-mp.mpf(5)/2)*leg(-24,Q)*e24(3*(Q-1))
    def TF(z):
        s=mp.mpf(Q)**(2*k-3)*F(Q*Q*z)
        s+=cM*sum(leg(b,Q)*F(z+mp.mpf(24*b)/Q) for b in range(Q))
        s+=mp.mpf(Q)**-2*sum(F((z+24*b)/mp.mpf(Q*Q)) for b in range(Q*Q))
        return s
    H=lambda z: eta(z)*TF(z)
    z=mpc(0.13,0.9)
    print(Q, abs(H(-1/z)-z**k*H(z))/abs(H(z)), abs(H(z+1)-H(z))/abs(H(z)))
    g=sum(leg(b,Q)*exp(2*pi*I*b/Q) for b in range(Q))
    s=leg(12,Q)*leg((-1)**(k-1),Q)
    print(' cM*g / (s Q^(k-2)) =', cM*g/(s*mp.mpf(Q)**(k-2)))
run(5); run(7); run(11)
