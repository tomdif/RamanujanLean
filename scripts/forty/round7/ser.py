P=400
def th(N,e,c=1):
    o=[0]*P
    for k in range(-80,81):
        E=N*k*(k-1)//2+e*k
        if 0<=E<P: o[E]+=(-1)**(k%2)*(c**(k%2))
        elif E<0 and any(True for _ in []): pass
    return o
def thfull(N,e,c=1):
    # returns dict incl negative
    o={}
    for k in range(-80,81):
        E=N*k*(k-1)//2+e*k
        if E<P: o[E]=o.get(E,0)+(-1)**(k%2)*(c**(k%2))
    return o
def T(N,e,c=1):
    d=thfull(N,e,c); assert all(v==0 for k,v in d.items() if k<0) or True
    o=[0]*P
    for k,v in d.items():
        if 0<=k<P:o[k]+=v
        elif k<0 and v!=0: raise Exception("neg %s"%((N,e),))
    return o
def mul(a,b):
    o=[0]*P
    for i,x in enumerate(a):
        if x:
            for j in range(P-i):
                if b[j]: o[i+j]+=x*b[j]
    return o
def add(*xs):
    return [sum(t) for t in zip(*xs)]
def sc(c,a): return [c*x for x in a]
def sh(k,a): return [0]*k+a[:P-k]
