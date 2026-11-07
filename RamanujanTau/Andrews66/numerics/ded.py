from fractions import Fraction as Fr
import math
def saw(x): return Fr(0) if x.denominator==1 else x-math.floor(x)-Fr(1,2)
def s(h,k): return sum(saw(Fr(i,k))*saw(Fr(h*i,k)) for i in range(1,k))
bad=0; tot=0
for k in range(1,41):
    for h in range(2*k):
        if math.gcd(h,2*k)!=1: continue
        lhs = 2*s(h,k)-4*s(h,2*k) + k
        rhs = (k+1)//2 + Fr(h*(1+(-1)**k),4)
        d = lhs-rhs
        tot+=1
        if not (d.denominator==1 and d.numerator%2==0): bad+=1
print("termwise congruence 2s(h,k)-4s(h,2k)+k == floor((k+1)/2)+h(1+(-1)^k)/4 mod 2: failures",bad,"of",tot)
