# How b_ℓ(m) depends on ℓ (numerical study, 2026-10-29)

Scripts and logs are in `scripts/frontier/pattern/`. The method:
* Iterate L(b) in Katz coordinates with the level-1 U and D matrices (`katzmat.py`, `bstab.py`, `bigstab.py`).
* Compute the stable modules exactly as Krylov spans, with Smith invariants over ℤ/ℓ^m.
* Validate three ways:
  * truncation stability: N = PR+3 vs PR+6 agree everywhere;
  * zero mismatches against p(n) data (ℓ = 17, 23, 29, 31);
  * known cases reproduced: ℓ = 5, 11 (Watson/Atkin), ℓ = 7 (Watson's 7^{⌊b/2⌋+1}), ℓ = 13 (Atkin–O'Brien),
    and κ mod ℓ = 6, 6, 10, 5.

Definition: b_ℓ(m) is the least b at which the ℤ/ℓ^m-module spanned by {L(b′) : b′ ≥ b, b′ ≡ b (2)} stabilizes.
This is the module version, reconstructed; it reproduces Boylan–Webb's b₂₉(2) = 3 and b₂₉(3) = 5. It agrees
with the proportionality version whenever the stable module is free of rank 1.

## Findings (d = dim S_{ℓ−1})
| ℓ | d | m tested | b_ℓ(m) | stable module mod ℓ^m |
|---|---|---|---|---|
| 13, 17, 19, 23 | 1 | ≤ 16 | **m** (proved in Lean for b ≤ m) | free, rank 1 |
| 29, 31 | 2 | ≤ 16 | 2m−1 | free, rank 1 |
| 37–59 | 3–4 | ≤ 16 / ≤ 9 | 2m−1 | free, rank 2 |
| 61–229 (41 primes ≥ 29 in total) | 5–19 | ≤ 9 / 8 / 7 | 2m−1 | free, rank ⌈d/2⌉ |

* **b depends on d only through whether d = 1.** The guess m + (d−1) is false; for example b₂₉(9) = 17, not 10.
* **The stable rank is ⌈d/2⌉ = ⌊(ℓ+12)/24⌋**, which is the Folsom–Kent–Ono upper bound. The bound appears to
  be attained for every prime tested. The identity ⌈d/2⌉ = ⌊(ℓ+12)/24⌋ was checked for all ℓ < 2·10⁵.
* Mod ℓ on S_{ℓ−1}:
  * Ū is invertible.
  * rank D̄ = rank X̄ = ⌈d/2⌉, and rank X̄^k stays at ⌈d/2⌉. So S_{ℓ−1} = Im X̄ ⊕ ker X̄, with dim ker X̄ = ⌊d/2⌋.
  * For rank ≥ 2 the unit eigenvalues are distinct, sometimes irreducible over 𝔽_ℓ (ℓ = 47, 59). So the
    replacement for "L(b+2) ≡ κL(b)" is an order-r linear recurrence.
* Newton slopes of X:
  * d ≥ 2: ⌈d/2⌉ slopes 0, then exactly ⌊d/2⌋ slopes 1, then ≥ 2;
  * d = 1: 0, 2, 2, 4, … (no slope 1).

## Conjectural mechanism (heuristic)
* The error's leading digit lies in S_{ℓ−1} = Im X̄ ⊕ ker X̄.
* The Im part is absorbed. This is a matrix version of the κ-argument.
* The ker X̄ part (slope 1) gains only one power of ℓ per two steps, so b = 2m−1 as soon as ker X̄ ≠ 0,
  i.e. d ≥ 2.
* For d = 1 the kernel is 0, the next slope is 2, and b = m. This is the case proved in Lean.

**Conjecture.** For every prime ℓ ≥ 29 and m ≥ 1:
* b_ℓ(m) = 2m − 1;
* the stable modules are free of rank ⌊(ℓ+12)/24⌋, so the FKO bound is attained.

Possible route to a proof:
* show rank D̄|S_{ℓ−1} = ⌈d/2⌉;
* show X̄ is semisimple at 0;
* show the slope-1 component of L(1) is nonzero (this gives b ≥ 2m−1).

Status: computed exactly in a validated truncated model; conjectural beyond. The novelty of the
rank-attainment statement has not been checked against the literature.
