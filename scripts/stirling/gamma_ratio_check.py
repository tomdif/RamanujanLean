# Numerical check of the Stirling/GammaRatio inequalities (evidence level 4).
# (1) core: |G(z)| |z|^th / |G(z+th)| <= e^10   (Re z >= 1, 0<=th<=1)  -- report the max ratio
# (2) per-factor: |w+th| <= exp(th*(5/(x-1/2)-5/(x+1/2))) |w+1|^th |w|^(1-th)
# (3) Stirling shape: |G(s+it)| / (|t|^(s-1/2) e^{-pi|t|/2}) -> sqrt(2 pi)
import mpmath as mp
mp.mp.dps = 30
mx1 = 0; mx2 = -1e9
for x in [1, 1.1, 1.5, 2, 3, 5]:
    for t in [0, 0.5, 1, 3, 10, 30, 100, 1000]:
        z = mp.mpc(x, t)
        for th in [0, 0.1, 0.25, 0.5, 0.75, 0.9, 1]:
            r = abs(mp.gamma(z)) * abs(z)**th / abs(mp.gamma(z + th))
            mx1 = max(mx1, r)
            lhs = abs(z + th)
            rhs = mp.e**(th*(5/(x-0.5)-5/(x+0.5))) * abs(z+1)**th * abs(z)**(1-th)
            mx2 = max(mx2, lhs/rhs)
print("max |G(z)||z|^th/|G(z+th)| =", mp.nstr(mx1, 8), " (proved bound e^10 =", mp.nstr(mp.e**10, 8), ")")
print("max per-factor lhs/rhs =", mp.nstr(mx2, 8), " (proved <= 1)")
for s in [0.5, 1, 2.3]:
    print("s=%g:" % s, [mp.nstr(abs(mp.gamma(mp.mpc(s, t)))/(t**(s-0.5)*mp.e**(-mp.pi*t/2)), 6) for t in [10, 100, 1000]], "sqrt(2pi)=", mp.nstr(mp.sqrt(2*mp.pi), 6))
