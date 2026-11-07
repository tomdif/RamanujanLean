# Numerical check of the elementary sign argument for alpha(n) = [q^n] f(q).
N = 1500
def mul(a, b):
    c = [0]*(N+1)
    for i, x in enumerate(a):
        if x:
            for j in range(N+1-i):
                c[i+j] += x*b[j]
    return c
def inv_one_plus(a, sign):  # 1/(1 + sign*X^a)
    c = [0]*(N+1)
    for k in range(0, N+1, a): c[k] = (-sign)**(k//a)
    return c
# Q = coeffs of prod (1+q^{2k+1}), B = prod_{k>=1}
B = [0]*(N+1); B[0] = 1
for k in range(1, N):
    a = 2*k+1
    if a > N: break
    for i in range(N, a-1, -1): B[i] += B[i-a]
Q = [B[i] + (B[i-1] if i else 0) for i in range(N+1)]
# phi(q) = sum q^{m^2}/(-q^2;q^2)_m ; E = sum q^{m^2}/(q^2;q^2)_m
phi = [0]*(N+1); E = [0]*(N+1)
m = 0
pp = [1]+[0]*N; pm = [1]+[0]*N
while m*m <= N:
    if m >= 1:
        pp = mul(pp, inv_one_plus(2*m, 1)); pm = mul(pm, inv_one_plus(2*m, -1))
    for i in range(N+1-m*m):
        phi[i+m*m] += pp[i]; E[i+m*m] += pm[i]
    m += 1
assert E == Q, "Euler"
theta = [0]*(N+1); theta[0] = 1
k = 1
while k*k <= N: theta[k*k] = 2; k += 1
Bp = mul(Q, theta)
s = [Bp[n] - 2*phi[n] for n in range(N+1)]
# f(q) directly
f = [0]*(N+1); m = 0; pr = [1]+[0]*N
while m*m <= N:
    if m >= 1:
        pr = mul(pr, inv_one_plus(m, 1))
    sq = mul(pr, pr)
    for i in range(N+1-m*m): f[i+m*m] += sq[i]
    m += 1
assert all(s[n] == (-1)**(n+1)*f[n] for n in range(N+1))
print("f:", f[:12])
assert all(abs(phi[n]) <= Q[n] for n in range(N+1))
crude = [sum(theta[j]*Q[n-j] for j in range(1, n+1)) - Q[n] for n in range(N+1)]
print("crude<=0 at n in 1..N:", [n for n in range(1, N+1) if crude[n] <= 0])
print("s<=0:", [n for n in range(1, N+1) if s[n] <= 0])
assert all(B[n] <= (Q[n-2] if n >= 2 else 0) for n in range(1, N+1))
assert all(B[n-2] <= B[n] for n in range(3, N+1))
print("Q[:12]", Q[:12], "B[:12]", B[:12])
