# Frontier probes (2026-10-27)

## 1. Atkin–O'Brien beyond 13: `b_ℓ(m) = m` for ℓ = 17, 19, 23 (conjecture, strong numerics)

Notation (Boylan–Webb): `b_ℓ(m)` is the least `b` from which the generating functions `P_ℓ(b)` are
proportional mod `ℓ^m` along `b ↦ b+2`. Concretely,
`p((ℓ^{b+2}n+1)/24) ≡ K · p((ℓ^b n+1)/24) (mod ℓ^m)` for all `n`, at `b = m`.

* **Known.** Atkin–O'Brien (1967) prove `b₁₃(m) = m`. Boylan–Webb (Trans. AMS 2013) prove `b_ℓ(m) ≤ 2m − 1`
  for all `ℓ ≥ 5` (assuming `d_ℓ = 0`, verified for `ℓ ≤ 1300`), and remark that this bound is sharp in all
  computed cases with `ℓ ≥ 29`. For example, `b₂₉(2) = 3` and `b₂₉(3) = 5`.
* **New numerics** (`scripts/frontier/`, `p(n) mod 17⁵·19⁴·23⁴` for `n ≤ 10⁸` by FLINT series inversion).
  The exponent is exactly `m`: proportionality fails mod `ℓ^{m+1}`.

| ℓ | m = 1 | m = 2 | m = 3 | m = 4 |
|---|---|---|---|---|
| 13 (control, A–O) | K = 6 ✓ | K = 45 ✓ (A–O's value) | K = 214 ✓ | — |
| 17 | 6 ✓ (20354 tests) | 210 ✓ (1197) | 3678 ✓ (71) | 38069 ✓ (4) |
| 19 | 10 ✓ | 48 ✓ | 3658 ✓ (41) | — |
| 23 | 5 ✓ | 465 ✓ | 4697 ✓ (16) | — |
| 29, 31 | ✓ | ✗ (only mod ℓ) | | |
| 37, 41, 43, 47 | ✗ | | | |

* **Pattern.** `b_ℓ(m) = m` holds exactly for `ℓ ∈ {13, 17, 19, 23}`. These are precisely the primes with
  `dim S_{ℓ−1}(SL₂(ℤ)) = 1`. For ℓ = 29 and 31, `dim S_{ℓ−1} = 2` and the Boylan–Webb bound `2m − 1` is sharp.
* **Conjecture.** For ℓ ∈ {17, 19, 23} and all `m ≥ 1`,
  `p((ℓ^{m+2}n+1)/24) ≡ K_{ℓ,m} p((ℓ^m n+1)/24) (mod ℓ^m)`, with `ℓ ∤ K_{ℓ,m}`.
  I have not found this stated or proved in the literature (Atkin 1968 observed some instances). Proving it,
  for example by the Atkin–O'Brien / Garvan–Shomanov method at levels 17, 19 and 23 (`ATKIN13_PLAN.md`
  pipeline), would be a new theorem.

## 2. Dissection identities: classical
The level-13 formula `E(Q)²/(QE(Q¹³)²) = −1 − c₀c₁/Q − c₂c₁₂ − c₅c₉` is equivalent to
`U₁₃(q⁻¹⁴E(q)²) = −E(q¹³)² − 2q⁻¹E(q)²`. That is the Hecke relation for the CM eigenform `η(12τ)²`
(`a₁₃ = −2`, `χ(13) = 1`; checked in `eta2.py`). So it is not new. The analogous identities at other ℓ reduce
to the same eigenform: `a_ℓ = 0` unless `ℓ ≡ 1 (mod 12)`, and for example `a₃₇ = 2`.

## 3. Higher-order Turán (Jensen) thresholds
`N(d)` is the last `n` where the degree-`d` Jensen polynomial of `p` fails to be real-rooted
(`jensen.py`, exact Sturm counts, `n < 7000`):

| d | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| N(d) | 24 | 93 | 205 | 380 | 609 | 907 | 1268 | 1700 | 2209 | 2786 | 3454 | 4193 | 5017 |

`d ≤ 5` agree with the proved values (Chen–Jia–Wang; Larson–Wagner). For `d ≥ 6` these are numerical
thresholds. A proof for a fixed `d` needs effective Jensen-to-Hermite estimates; our Rademacher-limit error
bound (`LogConcaveTail`) is the right input.
