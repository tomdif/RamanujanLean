from fractions import Fraction
L=150
def mul(a,b):
    c=[0]*L
    for i,x in enumerate(a):
        if x:
            for j in range(L-i): c[i+j]+=x*b[j]
    return c
def inv(a):
    b=[0]*L; b[0]=1
    for m in range(1,L): b[m]=-sum(a[j]*b[m-j] for j in range(1,m+1))
    return b
def J(a):
    s=[1]+[0]*(L-1)
    for n in range(L):
        for t in (a+13*n, 13-a+13*n, 13+13*n):
            if t<L:
                f=[0]*L; f[0]=1; f[t]=-1; s=mul(s,f)
    return s
J={a:J(a) for a in range(1,7)}
E=[0]*L
for k in range(-40,41):
    e=k*(3*k-1)//2
    if 0<=e<L: E[e]+=(-1)**(k%2)
E13=[0]*L
for i in range(0,L,13): E13[i]=E[i//13]
# multiply both sides by Q*J1J2J3J4J5J6 * E13^2 to clear: LHS*Q*E13^2 = E^2
# check: E^2 * J1J2J3J4J5J6 = E13^2*( J4J6*J1J5*J4J6 ... ) do it directly as Laurent: 
P=mul(mul(J[1],J[5]),mul(J[2],J[3])); R=mul(J[4],J[6])
# RHS*Q = J4J6/(J2J3) - Q - Q J2J3/(J1J5) - Q^2 J1J5/(J4J6); multiply by J1J2J3J5J4J6 = P*R... 
# RHS*Q*(J1J5)(J2J3)(J4J6) = (J4J6)^2 J1J5 - Q*J1J5*J2J3*J4J6 - Q*(J2J3)^2 J4J6 - Q^2 (J1J5)^2 J2J3
A=mul(J[1],J[5]); B=mul(J[2],J[3]); C=mul(J[4],J[6])
def sh(a,k): return [0]*k+a[:L-k]
rhs=[x-y-z-w for x,y,z,w in zip(mul(mul(C,C),A), sh(mul(mul(A,B),C),13), sh(mul(mul(B,B),C),13), sh(mul(mul(A,A),B),26))]
lhs=mul(mul(E,E), mul(mul(A,B),C)); lhs=mul(lhs,inv(mul(E13,E13)))
print(lhs[:L-30]==rhs[:L-30], lhs[:8], rhs[:8])
