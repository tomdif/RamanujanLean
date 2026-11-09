#!/usr/bin/env python3
"""Lean generators for `QS` (RamanujanTau/Forty/QS.lean): sums of binary quadratic forms over Z² glued along
exact covers (Cao's proofs of Entries 3.18 and 3.19(ii)).

  gen_orth(tag, form, B)       QS(qmono form) = canonical theta-product sum (orthogonal cover, `QS_orth`)
  gen_sub(tag, form, B, r, I)  QS(qmono form) = Σ_i ± t^{E_i} QS(qmono form_i)   (any cover, `QS_sub`)
form = (A, Bq, C, d, e, δ1, δ2): Σ (−1)^{δ1 x + δ2 y} t^{A x² + 2Bq xy + C y² + d x + e y}.
"""
import sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from ecs import typeII, find_ecs, c2  # noqa: E402
from gen import ecs_def, theta_nf, canon_terms, lean_side, lean_int  # noqa: E402


def sub(form, B, r, i):
    A, Bq, C, d, e, s1, s2 = form
    b11, b12, b21, b22 = B
    x0, y0 = r[0] * i, r[1] * i
    sA = A * b11 ** 2 + 2 * Bq * b11 * b21 + C * b21 ** 2
    sB = A * b11 * b12 + Bq * (b11 * b22 + b12 * b21) + C * b21 * b22
    sC = A * b12 ** 2 + 2 * Bq * b12 * b22 + C * b22 ** 2
    sd = 2 * A * b11 * x0 + 2 * Bq * (b11 * y0 + b21 * x0) + 2 * C * b21 * y0 + d * b11 + e * b21
    se = 2 * A * b12 * x0 + 2 * Bq * (b12 * y0 + b22 * x0) + 2 * C * b22 * y0 + d * b12 + e * b22
    q0 = A * x0 ** 2 + 2 * Bq * x0 * y0 + C * y0 ** 2 + d * x0 + e * y0
    sg = (-1) ** ((s1 * x0 + s2 * y0) % 2)
    raw = (sA, sB, sC, sd, se, s1 * b11 + s2 * b21, s1 * b12 + s2 * b22)
    return raw, q0, sg


def norm(f):
    return f[:5] + (f[5] % 2, f[6] % 2)


def qm(f):
    return "qmono " + " ".join(lean_int(x) for x in f)


def gen_orth(tag, form, B, r=None, lo=None):
    A, Bq, C, d, e, de1, de2 = form
    rr, I, terms, ok = typeII(A, Bq, C, d, e, de1, de2, B, r, None, None if lo is None else [lo])
    assert ok, tag
    nm = f"B{tag}"
    M1 = 2 * (A * B[0] ** 2 + 2 * Bq * B[0] * B[2] + C * B[2] ** 2)
    M2 = 2 * (A * B[1] ** 2 + 2 * Bq * B[1] * B[3] + C * B[3] ** 2)
    hn = {M1: f"hm{M1}", M2: f"hm{M2}"}
    lemmas = set()
    tl = []
    for (i, E, Cc, t1, t2) in terms:
        tl.append((E, Cc, t1, t2))
        for (M, f, c) in (t1, t2):
            lem, _ = theta_nf(M, f, c, f"hm{M}")
            if lem:
                lemmas.add(lem)
    ct = canon_terms(tl)
    rhs = lean_side(ct, hn)
    n = len(I)
    expand = ", ".join(["sum_insert (by decide)"] * (n - 1) + ["sum_singleton"])
    out = ecs_def(nm, B, rr, I, f"`L{tag}`: ")
    out += f"""
theorem L{tag} : QS ({qm(form)}) = {rhs} := by
  have h := (QS_orth {' '.join(lean_int(x) for x in form)} {nm} hm{M1} hm{M2} (by norm_num [{nm}])
    (by norm_num [{nm}]) (by norm_num [{nm}])).2
  simp only [{nm}] at h
  rw [{expand}] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [{', '.join(sorted(lemmas)) if lemmas else 'mul_one'}] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h
"""
    return out, (M1, M2), ct


def gen_sub(tag, form, B, r, I):
    nm = f"B{tag}"
    parts = []
    rws = []
    for i in I:
        raw, q0, sg = sub(form, B, r, i)
        f = norm(raw)
        if raw[5:] != f[5:]:
            rws.append(f"qmono_par {' '.join(lean_int(x) for x in raw)} {f[5]} {f[6]} (by decide) (by decide)")
        parts.append((q0, sg, f))
    s = ""
    for idx, (q0, sg, f) in enumerate(parts):
        body = f"QS ({qm(f)})" if q0 == 0 else f"mono {lean_int(q0)} 1 * QS ({qm(f)})"
        if idx == 0:
            s = body if sg > 0 else f"-({body})"
        else:
            s += (" + " if sg > 0 else " - ") + body
    n = len(I)
    expand = ", ".join(["sum_insert (by decide)"] * (n - 1) + ["sum_singleton"]) if n > 1 else "sum_singleton"
    out = ecs_def(nm, B, r, I, f"`S{tag}`: ")
    rw_line = f"\n  simp only [{', '.join(rws)}] at h" if rws else ""
    out += f"""
theorem S{tag} : QS ({qm(form)}) = {s} := by
  have h := QS_sub {' '.join(lean_int(x) for x in form)} {nm} (fun i hi => by
    simp only [{nm}, mem_insert, mem_singleton] at hi
    rcases hi with {' | '.join(['rfl'] * n)} <;> exact qmono_summ _ _ _ _ _ _ _ (by norm_num [sA, {nm}])
      (by norm_num [sA, sB, sC, {nm}]))
  simp only [{nm}] at h
  rw [{expand}] at h
  norm_num [qf0, sA, sB, sC, sd, se] at h{rw_line}
  try simp only [mono_neg1] at h
  linear_combination h
"""
    return out, parts


if __name__ == "__main__":
    pass
