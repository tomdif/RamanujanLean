import json
eg=json.load(open('e_g.json')); ep=json.load(open('e_phi.json'))
M=len(eg[0])
def mul(a,b):
    c=[0]*M
    for i,x in enumerate(a):
        if x:
            for j in range(M-i): c[i+j]+=x*b[j]
    return c
def Eser(L,step=1):
    E=[0]*L
    for k in range(-200,201):
        e=step*(k*(3*k-1)//2)
        if 0<=e<L: E[e]+=(-1)**(k%2)
    return E
def inv(a):
    b=[0]*M; b[0]=1
    for m in range(1,M): b[m]=-sum(a[j]*b[m-j] for j in range(1,m+1))
    return b
E1=Eser(M);E13=Eser(M,13)
r=mul(E13,inv(E1)); G=[0]+mul(r,r)[:M-1]
Gp=[[1]+[0]*(M-1)]
for i in range(30): Gp.append(mul(Gp[-1],G))
def fit(f,maxdeg):
    f=f[:]; co=[]
    for i in range(maxdeg+1):
        c=f[i]; co.append(c)
        f=[x-c*y for x,y in zip(f,Gp[i])]
    return co, all(x==0 for x in f)
res={}
for name,e,deg in (('g',eg,lambda j:14-j),('phi',ep,lambda j:7)):
    for j in range(1,14):
        co,ok=fit(e[j],deg(j))
        print(name,j,ok,co)
        res[f'{name}{j}']=co
json.dump(res,open('modeq_coeffs.json','w'))
print('M',M)
