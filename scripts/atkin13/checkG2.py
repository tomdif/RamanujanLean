L=120
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
from collections import defaultdict
cls=defaultdict(lambda:[0]*L)
for k in range(-400,401):
    e=k*(3*k-1)//2
    if e//13<L: cls[e%13][e//13]+=(-1)**(k%2)
E=[0]*L
for k in range(-40,41):
    e=k*(3*k-1)//2
    if 0<=e<L: E[e]+=(-1)**(k%2)
E13=[0]*L
for i in range(0,L,13): E13[i]=E[i//13]
iE13=inv(E13)
C={r:mul(cls[r],iE13) for r in cls}
print({r:C[r][:5] for r in C})
# e2 = 78 - 13*(C0C1/Q + C2C12 + C5C9 ) ; C7 should be 1
t1=mul(C[0],C[1]); t1=t1[1:]+[0]
X=[a+b+c for a,b,c in zip(t1,mul(C[2],C[12]),mul(C[5],C[9]))]
# 1/G = E^2/(Q E13^2): Laurent with Q^{-1}
w=mul(E,iE13); w2=mul(w,w)
print('X  ', X[:10])
print('w2 ', w2[:10], '(1/G = w2/Q)')
