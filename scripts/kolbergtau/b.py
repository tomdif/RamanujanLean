def k(x,y): return (x**8 + x**7*y + 352*x**6*y**2 - 2483*x**5*y**3 + 4888*x**4*y**4 + 1260*x**4*y**2 - 2483*x**3*y**5 - 3780*x**3*y**3 + 352*x**2*y**6 + 1260*x**2*y**4 + 630*x**2*y**2 + x*y**7 + y**8)
def PA(n,d): return (-17418240*n**3*d+104509440*n**4*d-125411328*n**5*d+17418240*n**2*d**3-139345920*n**3*d**3+194088960*n**4*d**3+34836480*n**2*d**5-78382080*n**3*d**5+9676800*n**2*d**7)
import random
for _ in range(2000):
    d=random.randrange(1,10**6,2); e=random.randrange(1,10**6,2)
    n=d*e
    assert PA(n,d)+27648*d**11+PA(n,e)+27648*e**11 == 27648*(d-e)**2*(d+e)*k(d,e)
bad=0
for d in range(1,16,2):
  for m in range(16):
    v=m*m*(d+4*m)*k(d,d+8*m)
    if v%16: bad+=1; print(d,m,v%16)
print("bad",bad)
