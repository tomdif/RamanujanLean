import sys
from ser import *
PP=400
def S(k,a):
    o=[0]*P
    for i,x in enumerate(a):
        if i*k<P: o[i*k]+=x
    return o
def thd(N,e,c=1):
    o={}
    for k in range(-60,61):
        E=N*k*(k-1)//2+e*k
        o[E]=o.get(E,0)+(-1)**(k%2)*(c**(k%2))
    return o
def dmul(a,b,lim):
    o={}
    for i,x in a.items():
        if i>lim: continue
        for j,y in b.items():
            if i+j<=lim: o[i+j]=o.get(i+j,0)+x*y
    return {k:v for k,v in o.items() if v}
def dadd(*ds):
    o={}
    for d in ds:
        for k,v in d.items(): o[k]=o.get(k,0)+v
    return {k:v for k,v in o.items() if v}
def dsh(k,c,d): return {i+k:c*v for i,v in d.items()}
LIM=150
SA=dadd(dmul(thd(30,6),dadd(thd(330,143),dsh(11,1,thd(330,253))),LIM), dsh(1,-1,dmul(thd(30,12),dadd(thd(330,209),dsh(33,1,thd(330,319))),LIM)))
SA={k:v for k,v in SA.items() if k<=LIM-40}
print(sorted(SA.items())[:12])
