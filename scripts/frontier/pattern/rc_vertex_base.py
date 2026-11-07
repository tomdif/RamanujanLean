# Finite proof of the base of D3 (BL_SHARPNESS_PROOF section 4.10, Step 7).
# With n=l-1, a=w+n: for j=w-1 the count dM(a+(j-1)n) = dM(w)+new(w,l) and the height
# sum_{1<=t<=w-2} t*gr^t(a) = ((w-2)/2) new(w,l). On each class of (l mod 12, w mod 12) both sides are
# polynomials of degree <=1 in l and <=2 in w, so a grid of 2 values of l and 3 of w per class decides it.
from fractions import Fraction as F
def dM(k):return k//12+(0 if k%12==2 else 1)
def dimS0(k,l):
    mu=l+1;e2=1+(-1 if l%4==3 else 1);e3=1+(-1 if l%3==2 else 1)
    g=1+F(mu,12)-F(e2,4)-F(e3,3)-1
    return (k-1)*(g-1)+(F(k,2)-1)*2+e2*(k//4)+e3*(k//3)
def new(w,l):return dimS0(w,l)-2*(dM(w)-1)
tot=bad=0;cl={}
for l in range(5,400):
    if l%2==0 or l%3==0:continue
    n=l-1
    for w in range(4,200,2):
        a=w+n;j=w-1;tot+=1
        gr=lambda t:dM(a+t*n)-dM(a+(t-1)*n)
        N=new(w,l)
        c=dM(a+(j-1)*n)==dM(w)+N
        h=2*sum(t*gr(t) for t in range(1,j))==(w-2)*N
        cl.setdefault((l%12,w%12),[set(),set()]);cl[(l%12,w%12)][0].add(l);cl[(l%12,w%12)][1].add(w)
        if not(c and h):
            bad+=1
            if bad<9:print('FAIL',l,w,c,h)
print('grid points',tot,'fails',bad,'classes',len(cl),'min l values',min(len(v[0]) for v in cl.values()),'min w values',min(len(v[1]) for v in cl.values()))
