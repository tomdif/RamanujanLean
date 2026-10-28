# high-precision (python-int) version of bstab: b_l(m) for large m at small l
import sys, json
from katzmat import Katz
from zmod import smith, size
def matvec(M, v, mod): return [sum(a * b for a, b in zip(row, v)) % mod for row in M]
def run(p, PR, N, B, mlist):
    K = Katz(p, PR, N); U, D = K.matrices_list(); mod = K.mod
    vs = [[1] + [0] * (K.dN - 1)]
    for b in range(1, B + 1): vs.append(matvec(D if b % 2 else U, vs[-1], mod))
    out = {}
    for m in mlist:
        s = {}
        for b in range(1, B + 1):
            cols = []; last = -1
            for j in range(b, B + 1, 2):
                cols.append(vs[j]); sz = size(cols, p, m)
                if sz == last: s[b] = sz; break
                last = sz
        bmod = next((b for b in range(1, B - 1) if b in s and b + 2 in s and s[b] == s[b + 2]), None)
        out[m] = (bmod, s.get(bmod + 2) if bmod else None)
    return out
if __name__ == '__main__':
    p, PR, N, B = map(int, sys.argv[1:5]); ms = list(range(1, PR + 1))
    r = run(p, PR, N, B, ms)
    print(f'l={p} PR={PR} N={N}:', ' '.join(f'm={m}:b={r[m][0]}(|stab|=l^{r[m][1]})' for m in ms), flush=True)
