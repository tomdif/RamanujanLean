# f = q E(q^12)^2 = eta(12 tau)^2 ; test U_l f = a_l f - chi(l) f(q^l)
L=200000
E=[0]*L
for k in range(-400,401):
    e=k*(3*k-1)//2
    if 0<=e and 12*e<L: E[12*e]+=(-1)**(k%2)
# E(q^12)^2 via convolution sparse
nz=[i for i,x in enumerate(E) if x]
f=[0]*L
for i in nz:
    for j in nz:
        if 1+i+j<L: f[1+i+j]+=E[i]*E[j]
for l in (5,7,11,13,17,19,23,29,31,37):
    a=f[l]; U=[f[l*n] for n in range(L//l)]
    M=L//(l*l)
    chi=None
    for c in (1,-1,0):
        if all(U[n]==a*f[n]-c*(f[n//l] if n%l==0 else 0) for n in range(M)): chi=c
    print(l,'a_l =',a,'chi =',chi)
