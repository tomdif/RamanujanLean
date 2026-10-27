def c2(k): return k*(k-1)//2
T={13:('one',None)}
for a in range(1,7): T[13+3*a]=('A',a); T[26+3*a]=('B',a)
res=[]
for rho in range(13):
    e=3*c2(-rho)-rho; x=19-3*rho; sign=(-1)**rho; ops=[]
    for _ in range(10):
        if x in T: break
        if 39-x in T: ops.append(('refl',x)); x=39-x; continue
        # shift: Pt(x) = mono(d x)(-1) Pt(x+39)  -> exponent += 13x, sign *= -1
        ops.append(('shift',x)); e+=13*x; sign=-sign; x=x+39
    res.append((rho,e,sign,x,T.get(x),ops))
    print(rho,'e',e,'sign',sign,'Pt',x,T.get(x),ops)
