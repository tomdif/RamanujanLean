# Counting the n with τ(n) ≠ 0: lower bounds (2026-11-04)

Lean directory: `RamanujanTau/TauDensity/` (`Structure.lean`, `Analytic.lean`, `Proportion.lean`, `Main.lean`).
Numerics: `scripts/taudensity/validate.gp`.
Build: `lake build RamanujanTau.TauDensity.Main` (exit 0). No `sorry`, `native_decide` or new axiom is used.
Every headline below prints `[propext, Classical.choice, Quot.sound]`.

Notation: `Z(N) = #{n ∈ [1,N] : τ(n) ≠ 0}`.

## Headlines

| # | Theorem | Statement | Inputs | Evidence |
|---|---------|-----------|--------|----------|
| 1 | `tau_pointwise_weil` | ∀ε>0 ∃C>0 ∀n≥1, \|τ(n)\| ≤ C n^{23/4+ε} | `StepanovAS.tau_isBigO_23_4_unconditional` | (1) axiom-clean |
| 2 | `card_tau_ne_zero_ge_rpow` | ∀ε>0 ∃c>0 ∀N≥1, c·N^{1/2−ε} ≤ Z(N) | #1 + `RankinSelberg.rankinSelberg_two_sided` | (1) |
| 3 | `tau_prime_pow_eq_zero_iff` | τ(p^k)=0 ↔ τ(p)=0 ∧ k odd | Lehmer's lemma + Hecke recurrence | (1) |
| 4 | `tau_eq_zero_iff` | n≥1: τ(n)=0 ↔ ∃p prime, v_p(n) odd ∧ τ(p)=0 | #3 + multiplicativity | (1) |
| 5 | `tau_sq_ne_zero` | τ(m²) ≠ 0 for every m ≥ 1 | #4 | (1) |
| 6 | `card_tau_ne_zero_ge_sqrt` | ⌊√N⌋ ≤ Z(N) for every N | #5 | (1) |
| 7 | `prime_zero_candidate` | τ(p)=0 ⇒ p ≥ 21 492 863 999, p ≡ −1 mod 10 746 432 000 = 2⁹3⁵5³691, p ≡ 3,5,6 mod 7 | `LehmerSmall` congruences + `lehmer_below_21492863999` | (1) |
| 8 | `tau_ne_zero_of_mod691` | τ(n)≠0 if no prime p ≡ −1 (mod 691) divides n to an odd power | #4 + mod-691 congruence | (1) |
| 8′ | `tau_ne_zero_of_prime_factors_mod691` | τ(n)≠0 if no prime factor of n is ≡ −1 (mod 691) | #8 | (1) |
| 8″ | `tau_ne_zero_of_no_candidate` | τ(n)≠0 unless an odd-exponent prime of n satisfies all of #7 | #4, #7 | (1) |
| 9 | `tau_small_mul_sq_ne_zero` | τ(s·m²) ≠ 0 for 1 ≤ s < 21 492 863 999, m ≥ 1 | #8″ | (1) |
| 10 | `card_tau_ne_zero_ge` | max(⌊√N⌋, min(N, 21 492 863 998)) ≤ Z(N) | #6 + Lehmer range | (1) |
| 11 | `card_tau_eq_zero_le` | #{n ≤ N : τ(n)=0} ≤ N(1+log N)/10 746 432 000 | #4, #7, `harmonic_le_one_add_log` | (1) |
| 12 | `card_tau_ne_zero_ge_proportion` | N(1 − (1+log N)/10 746 432 000) ≤ Z(N) | #11 | (1) |
| 13 | `card_tau_ne_zero_ge_nine_tenths` | log N ≤ 10⁹ ⇒ 0.9·N ≤ Z(N) | #12 | (1) |

## Proofs, briefly

**#2 (Weil + Rankin–Selberg).** Use #1 with ε/2, so τ(n)²/n¹¹ ≤ C² n^{1/2+ε}. Terms with τ(n) = 0 contribute
nothing, so `c₁N ≤ Σ_{n≤N} τ(n)²/n¹¹ ≤ Z(N)·C²·N^{1/2+ε}`. Hence `Z(N) ≥ (c₁/C²) N^{1/2−ε}`.

**#3–#5 (the zero set).** If τ(p) = 0, the Hecke recurrence becomes τ(p^{k+2}) = −p¹¹τ(p^k). That gives
τ(p^{2j}) = (−p¹¹)^j ≠ 0 and τ(p^{2j+1}) = 0. If τ(p) ≠ 0, Lehmer's lemma (`LehmerSmall.tau_prime_pow_ne_zero`)
gives τ(p^k) ≠ 0 for all k. Multiplicativity then gives #4. Every exponent of a square is even, which gives #5.

**#8 (mod 691).** τ(p) ≡ 1 + p¹¹ (mod 691). Because gcd(11, 690) = 1, the map x ↦ x¹¹ is a bijection of 𝔽₆₉₁,
so 1 + x¹¹ = 0 has only the root x = −1 (kernel `decide`, `LehmerSmall.d691`). So τ(p) = 0 forces p ≡ −1 (mod 691).
By #4, only primes with odd exponent matter.

**#11.** If τ(n) = 0, some prime p ∣ n has τ(p) = 0. By #7 that prime has the form p = iM + (M−1) with
M = 10 746 432 000 and 1 ≤ i ≤ N. So
#zeros ≤ Σ_{i≤N} ⌊N/(iM+M−1)⌋ ≤ (N/M)·H_N ≤ N(1+log N)/M.

## What the results say

* **The elementary bound beats the analytic one.** #6 gives ⌊√N⌋ ≤ Z(N), and #2 gives c_ε N^{1/2−ε}. The
  Weil + Rankin–Selberg route only reaches the 1/2 exponent up to ε, while τ(m²) ≠ 0 alone gives exactly √N.
  Even Deligne's bound in place of Weil would only improve #2 to N^{1/2}/(log N)^{O(1)}. The method is limited
  by τ(n)²/n¹¹ ≲ n^{1/2}, so it can never beat √N. Pushing the analytic route further needs a higher moment,
  which is not available here.
* **Positive proportion, in a huge but finite range.** #12–#13 give Z(N) ≥ 0.9 N for every N ≤ e^{10⁹}. For
  N ≤ 10²⁰ the zero count is at most about 5·10⁻⁹·N. Asymptotically the bound fails, because it only counts
  integers in the class −1 mod M, not primes, and Σ 1/(iM) diverges.
* **The truth (literature, evidence level 3).** Serre (1981, *Quelques applications du théorème de densité de
  Chebotarev*, §7) proved #{p ≤ x : τ(p) = 0} ≪ x/(log x)^{3/2−δ}. So Σ_{τ(p)=0} 1/p < ∞, and by #4 the set
  {n : τ(n) ≠ 0} has natural density ∏_{τ(p)=0} (1 − 1/(p+1)) > 0. Lehmer's conjecture says this density is 1.
  Making Serre's argument formal needs Chebotarev and the open image of the mod-ℓ Galois representations.
  That is far beyond the repo.
* **An N^{1−ε} route (not done).** If p ∣ x² + 691y² with gcd(x, 691y) = 1 and p ≠ 2, then (−691/p) = 1. That
  means (p/691) = 1, so p is a square mod 691, while −1 is not (691 ≡ 3 mod 4). So every value x² + 691y²
  (gcd(x, 691y) = 1) avoids primes ≡ −1 (mod 691) and has τ ≠ 0 by #8′. The values up to N number about N^{1−ε}
  (≫ N/(log N)^{1/2} by Landau–Bernays). Formalising this needs quadratic reciprocity (in Mathlib) plus a
  representation-multiplicity bound r(n) ≪ n^ε, or a second-moment count. Estimate: 1–2 days of Lean.

## Numerical validation (evidence level 4; `validate.gp`, PARI, N = 2·10⁵, about 2 min)

* τ(n) ≠ 0 for all n ≤ 2·10⁵ (Z(N) = N).
* τ(p) ≡ 1 + p¹¹ (mod 691) for all p ≤ 2·10⁵, with 0 failures. The only root of 1 + x¹¹ mod 691 is x = 690.
* τ(p²) = τ(p)² − p¹¹ for p ≤ 400. τ(m²) ≠ 0 for m ≤ 447.
* Rankin–Selberg ratio (1/N)Σ τ(n)²/n¹¹ at N = 2·10⁵ is 0.38402 (Zagier constant 0.38408). The minimum
  over N ≤ 2·10⁵ is 0.35925 (the empirical c₁).
* max_n |τ(n)|/n^{23/4+1/20} = 1 and max_n |τ(n)|/(d(n)n^{11/2}) = 1, both attained at n = 1. So the
  implied constant in #2 with ε = 1/10 is empirically c ≈ 0.359.
* 21 492 863 999 is prime, ≡ 5 (mod 7), and τ(21 492 863 999) ≠ 0. It is the first number the proved
  congruences of #7 cannot exclude.

## Gaps / next steps

* An asymptotic positive proportion (Serre) is out of reach: it needs Chebotarev and ℓ-adic images.
* N^{1−ε} through the norm form x² + 691y², as sketched above: about 1–2 days.
* An explicit constant in #2 needs explicit c₁ (Rankin–Selberg) and explicit C (Weil), which the upstream
  existence proofs do not export.
