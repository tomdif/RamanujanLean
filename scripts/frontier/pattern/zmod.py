# linear algebra over Z/l^m (Z_l truncated): Smith invariants, span size, membership
def val(x, l, cap):
    if x == 0: return cap
    c = 0
    while x % l == 0 and c < cap: x //= l; c += 1
    return c

def smith(cols, l, m):
    """cols: list of vectors (lists) over Z/l^m. Returns sorted list of invariant-factor valuations
    e_i < m (module span ≅ ⊕ Z/l^{m-e_i})."""
    mod = l ** m
    A = [[x % mod for x in c] for c in cols]  # rows = generators
    if not A: return []
    nr, nc = len(A), len(A[0])
    inv = []
    r0 = 0
    rows = list(range(nr)); colsidx = list(range(nc))
    A = [row[:] for row in A]
    while True:
        best = None; bv = m
        for i in range(r0, nr):
            for j in range(r0, nc):
                x = A[i][j]
                if x:
                    v = val(x, l, m)
                    if v < bv:
                        bv = v; best = (i, j)
                        if v == 0: break
            if bv == 0: break
        if best is None: break
        i, j = best
        A[r0], A[i] = A[i], A[r0]
        for row in A: row[r0], row[j] = row[j], row[r0]
        piv = A[r0][r0]; u = piv // l ** bv; ui = pow(u, -1, mod)
        A[r0] = [x * ui % mod for x in A[r0]]   # now pivot = l^bv
        # eliminate column r0 in other rows, row r0 in other cols
        for i2 in range(nr):
            if i2 != r0 and A[i2][r0]:
                c = A[i2][r0] // l ** bv
                A[i2] = [(x - c * y) % mod for x, y in zip(A[i2], A[r0])]
        # row r0 entries are multiples of l^bv (pivot minimal); clearing them by column ops
        # doesn't affect invariants
        for j2 in range(nc):
            if j2 != r0: A[r0][j2] = 0
        inv.append(bv); r0 += 1
        if r0 >= min(nr, nc): break
    return sorted(inv)

def size(cols, l, m):
    return sum(m - e for e in smith(cols, l, m))
