#!/usr/bin/env python3
"""Regenerate the coordinate table for the prime-607 proof.

The table is untrusted: Lean checks every step against the kernel-computed rows
in `Rank607Final`. The matrix is read from the saved witness record.
"""
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
Q = 607 ** 2
SIZE = 102


def read_rows():
    text = subprocess.run(['lake', 'env', 'lean', 'scripts/rank607_dump.lean'], cwd=ROOT,
                          check=True, capture_output=True, text=True).stdout
    phi, low, up, down = None, [], [], []
    for line in text.splitlines():
        if line.startswith('PHI '):
            phi = [v % Q for v in json.loads(line[4:])]
        elif line.startswith('R '):
            a, b, c = line[2:].split(' | ')
            low.append([v % Q for v in json.loads(a)])
            up.append([v % Q for v in json.loads(b)])
            down.append([v % Q for v in json.loads(c)])
    assert phi is not None and len(low) == SIZE
    return phi, low, up, down


def coordinates(prefix, low):
    rest = list(prefix)
    out = [0] * SIZE
    for t in range(SIZE):
        out[t] = rest[t]
        for j in range(t, SIZE):
            rest[j] = (rest[j] - out[t] * low[t][j]) % Q
    return out


P_ = 607


def solve_mod_p(cols, target):
    n = len(cols)
    rows = [[cols[j][k] % P_ for j in range(n)] + [target[k] % P_] for k in range(SIZE)]
    piv, r0 = [], 0
    for c in range(n):
        rr = next(r for r in range(r0, SIZE) if rows[r][c])
        rows[r0], rows[rr] = rows[rr], rows[r0]
        iv = pow(rows[r0][c], -1, P_)
        rows[r0] = [v * iv % P_ for v in rows[r0]]
        for r in range(SIZE):
            if r != r0 and rows[r][c]:
                f = rows[r][c]
                rows[r] = [(v - f * w) % P_ for v, w in zip(rows[r], rows[r0])]
        piv.append(r0)
        r0 += 1
    assert all(rows[r][n] == 0 for r in range(r0, SIZE))
    return [rows[piv[c]][n] for c in range(n)]


def solve_dual(vecs, rhs):
    """Find phi over F_p with phi . vecs[i] = rhs[i] (vecs independent mod p)."""
    n = len(vecs)
    rows = [[vecs[i][k] % P_ for k in range(SIZE)] + [rhs[i] % P_] for i in range(n)]
    pivs = []
    for i in range(n):
        c = next(c for c in range(SIZE) if rows[i][c])
        iv = pow(rows[i][c], -1, P_)
        rows[i] = [v * iv % P_ for v in rows[i]]
        for r in range(n):
            if r != i and rows[r][c]:
                f = rows[r][c]
                rows[r] = [(v - f * w) % P_ for v, w in zip(rows[r], rows[i])]
        pivs.append(c)
    phi = [0] * SIZE
    for i, c in enumerate(pivs):
        phi[c] = rows[i][SIZE]
    return phi


def inverse_mod(A):
    n = len(A)
    M = [row[:] + [int(i == k) for k in range(n)] for i, row in enumerate(A)]
    for c in range(n):
        r = next(r for r in range(c, n) if M[r][c] % P_)
        M[c], M[r] = M[r], M[c]
        iv = pow(M[c][c], -1, Q)
        M[c] = [v * iv % Q for v in M[c]]
        for r in range(n):
            if r != c and M[r][c]:
                f = M[r][c]
                M[r] = [(v - f * w) % Q for v, w in zip(M[r], M[c])]
    return [row[n:] for row in M]


def structure_certificate(table, C):
    """Untrusted certificates for the precision-two module structure."""
    coord = lambda b: table[b - 1]
    Ai = inverse_mod([row[:24] for row in C[:24]])
    t = [sum(Ai[i][k] * C[k][24] for k in range(24)) % Q for i in range(24)]
    rAi = [sum(C[24][k] * Ai[k][j] for k in range(24)) % Q for j in range(24)]
    P = [Ai[i] + [0] for i in range(24)] + [[(-v) % Q for v in rAi] + [1]]
    last = (C[24][24] - sum(C[24][k] * t[k] for k in range(24))) % Q
    assert last % P_ == 0 and (last // P_) % P_
    u = last // P_
    V = [coord(2 * j + 3) for j in range(24)]
    w = [((coord(51)[k] - sum(t[j] * V[j][k] for j in range(24))) % Q) for k in range(SIZE)]
    assert all(v % P_ == 0 for v in w)
    x0 = solve_mod_p(V, coord(53))
    res = [(coord(53)[k] - sum(x0[j] * V[j][k] for j in range(24))) % Q for k in range(SIZE)]
    sol = solve_mod_p(V + [[v // P_ for v in w]], [v // P_ for v in res])
    y = sol[24]
    rel = [((x0[j] + P_ * sol[j]) - y * t[j]) % Q for j in range(24)] + [y]
    rel1 = solve_mod_p(V, coord(1))
    Ap = [[v % P_ for v in row[:24]] for row in C[:24]]
    M = [row[:] + [int(i == k) for k in range(24)] for i, row in enumerate(Ap)]
    for c in range(24):
        r = next(r for r in range(c, 24) if M[r][c])
        M[c], M[r] = M[r], M[c]
        iv = pow(M[c][c], -1, P_)
        M[c] = [v * iv % P_ for v in M[c]]
        for r in range(24):
            if r != c and M[r][c]:
                f = M[r][c]
                M[r] = [(v - f * w) % P_ for v, w in zip(M[r], M[c])]
    K = [row[24:] for row in M]
    # A functional on coordinates vanishing on L(3), ..., L(51) but not on L(1).
    wp = [v // P_ for v in w]
    r1 = [(coord(1)[k] - sum(rel1[j] * V[j][k] for j in range(24))) % Q for k in range(SIZE)]
    assert all(v % P_ == 0 for v in r1)
    r1p = [v // P_ for v in r1]
    vecs = V + [wp, r1p]
    phibar = solve_dual(vecs, [0] * 25 + [1])
    e = [(sum(phibar[k] * V[j][k] for k in range(SIZE)) % Q) // P_ for j in range(24)]
    psi = solve_dual(V, [(-v) % P_ for v in e])
    phi = [(a + P_ * b) % Q for a, b in zip(phibar, psi)]
    for j in range(25):
        assert sum(phi[k] * coord(2 * j + 3)[k] for k in range(SIZE)) % Q == 0
    assert sum(phi[k] * coord(1)[k] for k in range(SIZE)) % Q != 0
    return {'t': t, 'P': P, 'u': u, 'uinv': pow(u, -1, Q), 'rel': rel, 'rel1': rel1, 'K': K,
            'phi': phi}


def generate():
    phi, low, up, down = read_rows()
    prefix, table, prefixes = phi, [], {}
    for b in range(1, 54):
        prefixes[b] = prefix
        d = coordinates(prefix, low)
        table.append(d)
        rows = up if b % 2 == 1 else down
        prefix = [sum(d[t] * rows[t][j] for t in range(SIZE)) % Q for j in range(SIZE)]
    matrix = json.loads((ROOT / 'docs/verification/rank607-uniform-n2.json').read_text())['witness_matrix']
    assert [[prefixes[2 * j + 3][i + 26] for j in range(25)] for i in range(25)] == matrix
    cert = structure_certificate(table, matrix)
    fmt = lambda rows: '[\n  ' + ',\n  '.join('[' + ', '.join(map(str, r)) + ']' for r in rows) + ']'
    return f'''import Mathlib.Data.Nat.Notation

/-! Coordinates of `L(1), ..., L(53)` in the reconstruction basis, the saved minor,
and the precision-two structure certificates.
Generated by `scripts/generate_rank607_coords.py`. Lean checks all of this data. -/
namespace RamanujanTau.FiniteArithmetic.Rank607Program
set_option maxRecDepth 100000

/-- `coordTable[b-1]` holds the coordinates of `L(b)`. -/
def coordTable : List (List ℕ) := {fmt(table)}

/-- `matrixTable[i][j]` is coefficient `i + 26` of `L(2 j + 3)`. -/
def matrixTable : List (List ℕ) := {fmt(matrix)}

/-- `t`: the last column of the minor modulo the leading block. -/
def tTable : List ℕ := [{', '.join(map(str, cert['t']))}]

/-- Elimination matrix with `P * minor = [[I, t], [0, 607 u]]`. -/
def pTable : List (List ℕ) := {fmt(cert['P'])}

/-- `L(53) = Σ rel_j L(2 j + 3)`. -/
def relTable : List ℕ := [{', '.join(map(str, cert['rel']))}]

/-- `L(1) ≡ Σ rel1_j L(2 j + 3) (mod 607)`. -/
def rel1Table : List ℕ := [{', '.join(map(str, cert['rel1']))}]

/-- Inverse modulo 607 of the leading 24-by-24 block of the minor. -/
def kTable : List (List ℕ) := {fmt(cert['K'])}

/-- A coordinate functional vanishing on `L(3), …, L(51)` but not on `L(1)`. -/
def phiTable : List ℕ := [{', '.join(map(str, cert['phi']))}]

/-- The unit `u` in the last pivot `607 u`, and its inverse. -/
def uVal : ℕ := {cert['u']}
def uInv : ℕ := {cert['uinv']}

end RamanujanTau.FiniteArithmetic.Rank607Program
'''


if __name__ == '__main__':
    path = ROOT / 'RamanujanTau/FiniteArithmetic/Rank607Coords.lean'
    path.write_text(generate())
    print(path)
