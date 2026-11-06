"""Asymptotic profile of SKQFHyp (ii): F(K,theta) = lim_{y->oo} max_L |I|/h^2.
Scaling: with l = log y, h = K theta / l and L = l/theta - O(1), I/h^2 depends only on (K, theta)
in the limit; we fit I/h^2 = A + B/l + C/l^2 over the available y and report A, sqrt(K) A, K A."""
import numpy as np, post
ys = [30, 60, 100, 200]
data = {y: post.load(y) for y in ys}
for th in (0.25, 0.1, 0.05):
    print('=== theta = %.3f ===' % th)
    for K in (1, 2, 4, 8, 16, 32, 64):
        vals = []
        for y in ys:
            v, S, S0 = data[y]; l = np.log(y); logT = l / th; h = K / logT
            if h > v[-1]: break
            Ls = np.linspace(logT - np.log(4 * np.pi), logT, 41)
            vals.append(max(abs(post.Ival(v, S, S0, h, L)) for L in Ls) / h**2)
        if len(vals) < len(ys): continue
        ls = np.log(np.array(ys, float))
        M = np.vstack([np.ones_like(ls), 1 / ls, 1 / ls**2]).T
        A, B, C = np.linalg.lstsq(M, np.array(vals), rcond=None)[0]
        A2 = np.polyfit(1 / ls, vals, 1)[1]
        print('  K=%3d  I/h^2(y=30..200) = %s   A(quad)=%.3f A(lin)=%.3f  sqrtK*A=%.2f  K*A=%.2f'
              % (K, ' '.join('%.4f' % x for x in vals), A, A2, np.sqrt(K) * A, K * A))
