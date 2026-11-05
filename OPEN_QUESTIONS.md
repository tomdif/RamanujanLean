# The τ arc — closure status

For the whole repository, including finite arithmetic and current research gaps,
see [Current status](docs/STATUS.md). This document concerns the τ arc only.

This file is the definitive accounting of every question the `τ` arc leaves open. Each is *closed* in the
sense that matters for a formalization project: it is pinned to an exact, named missing lemma and classified
as **reachable** (buildable on today's Mathlib) or **infrastructure-gap** (needs objects Mathlib does not yet
have). Nothing below is asserted as an `axiom`; unreachable inputs enter proved theorems as explicit,
named hypotheses — the same discipline used for `TauMultiplicativity`, `DeligneBound`, `LehmerConjecture`.

## 1. The mod-691 congruence — CLOSED (unconditional theorem proved)

**Question.** Is `τ(n) ≡ σ₁₁(n) (mod 691)` provable on Mathlib's modular-forms library?

**Status. Fully proved, unconditionally, kernel-clean.**

- `Mod691.tau_mod_relation` — `691·[qⁿ]E₄³ = 65520·σ₁₁(n) + 432000·τ(n)` (identity in `ℂ`), read off the
  `M₁₂` relation `E₄³ = E₁₂ + (432000/691)·Δ`. Scalar pinned by `coeff 1 = 1` (`DiscriminantBridge`).
- `Mod691.tau_int` — **`τ(n) ∈ ℤ`**, proved outright: `E₄`, `E₆` are the images of explicit integer series
  `p₄ = 1 + 240·∑σ₃`, `p₆ = 1 − 504·∑σ₅` (`qExpansion_E4_eq`/`qExpansion_E6_eq`), so `1728·τ(n) = [qⁿ](p₄³−p₆²)`;
  and `key_dvd` shows `1728 ∣ [qⁿ](p₄³−p₆²)` — the `A²,A³,B²` terms carry a factor `1728`, and the linear term
  `144·(5σ₃(n)+7σ₅(n))` is handled by `sigma_dvd` (`12 ∣ 5σ₃+7σ₅`, from `12 ∣ 5d³+7d⁵` per divisor, decided in
  `ZMod 12`). This is the classical integrality of `Δ = (E₄³−E₆²)/1728`, now formalized.
- `Mod691.tau_congruence_mod691_unconditional` — for `n ≥ 1`, an integer `τ(n)` equal to `[qⁿ]qExpansion(Δ)`
  with `τ(n) ≡ σ₁₁(n) (mod 691)`. No hypotheses, no `axiom`s beyond `propext, Classical.choice, Quot.sound`.

There is **no** remaining input on the modular side: this is a complete formal proof of Ramanujan's mod-691
congruence for the modular discriminant's q-expansion coefficients.

## 2. The general product bridge `[qⁿ]∏(1−qⁿ)²⁴ = τ(n)` — CLOSED (proved, 2026-10-04)

**Question.** Can Mathlib's *analytic* `Δ = η²⁴` be identified coefficient by coefficient with the *formal*
Euler product `q·∏(1−qⁿ)²⁴`?

**Status. Proved, axiom-clean** (`RamanujanTau.DiscriminantBridge.qExpansion_discriminant_coeff` in `DiscriminantQExpansion.lean`). The earlier verdict
("infrastructure gap") was wrong: the bridge does not need an analytic-product → `FormalMultilinearSeries`
lemma. The proof avoids it as follows:

- The polynomial partial products `F_N(q) = q(∏_{k<N}(1−qᵏ⁺¹))²⁴` converge locally uniformly on the unit disc
  to the cusp function of `Δ`. This uses Mathlib's `multipliableLocallyUniformlyOn_one_sub_pow` and
  `TendstoLocallyUniformlyOn.mul₀`.
- Weierstrass (`TendstoLocallyUniformlyOn.deriv`, iterated) gives `iteratedDeriv n F_N 0 → iteratedDeriv n Δ 0`.
- For polynomials, `iteratedDeriv n F_N 0 = n!·[qⁿ]F_N`. Once `N > n`, this coefficient is `τ(n)`
  (coefficient stabilization), so the limit is `n!·τ(n)`.

Consequences (`TauModular`):
- the mod-691 congruence for the combinatorial and computable `τ` (`tau_computable_mod691`);
- the integer identity `1728·q(q;q)²⁴_∞ = E₄³ − E₆²` in `ℤ⟦q⟧` (`discriminant_formal_identity`).

## 3. `τ` multiplicativity — CLOSED (proved, 2026-10-04); size of `τ`: Weil's bound proved, Deligne open here; Lehmer — partial

- **Multiplicativity and the Hecke recurrence are proved** (`RamanujanTau.tau_mul_coprime` in `HeckeQExp.lean`,
  `tau_hecke_recurrence`; axiom-clean). `HeckeCore`/`HeckeForm` build `T_p` on `CuspForm 𝒮ℒ k` by the
  elementary coset computation, without Mathlib's double-coset machinery. `HeckeQExp` computes its
  q-expansion, which gives a `HeckeData` term and an instance of `TauHeckeMaster`.
- **Bounds on `|τ(n)|`.** Hecke's `τ(n) = O(n⁶)` (`tau_isBigO`, `TauLSeries.lean`) has been improved, unconditionally
  and axiom-clean, three times (2026-11-03/04): Kloosterman's `O(n^{47/8+ε})`
  (`TauBound.tau_isBigO_47_8_unconditional`), Salié's `O(n^{35/6+ε})` (`Stepanov.tau_isBigO_35_6_unconditional`), and
  **Weil's `O(n^{23/4+ε})`** (`StepanovAS.tau_isBigO_23_4_unconditional`, via Weil's Kloosterman bound
  `StepanovAS.weilPrimeBound`). See [TAU_SUBHECKE_BOUND](docs/TAU_SUBHECKE_BOUND.md),
  [STEPANOV](docs/STEPANOV.md), [STEPANOV_ARTIN_SCHREIER](docs/STEPANOV_ARTIN_SCHREIER.md). (Rankin's 1939 `29/5`
  lies between 35/6 and 23/4 and is not formalized.)
- `DeligneBound` states Deligne's bound (`|τ(p)| ≤ 2p^{11/2}`) as a named hypothesis; its proof is not formalized
  here (it needs the Weil conjectures).
- `LehmerConjecture` (`τ(n) ≠ 0`) is a famous open problem. The finite range `τ(n) ≠ 0` for `1 ≤ n < 214,928,639,999`
  (Lehmer 1947) is proved (`LehmerSmall.lehmer_below_214928639999`; see [LEHMER_SMALL_N](docs/LEHMER_SMALL_N.md)).

Deligne and Lehmer are documented as hypotheses, not defects.

**Hecke's functional equation (2026-11-04).** `HeckeL.heckeLambda_entire` and `HeckeL.heckeLambda_functional_equation`: Λ(s) = (2π)^{−s}Γ(s)L(Δ,s) is entire with Λ(12−s) = Λ(s), so L(Δ,s) is entire (`HeckeL.tauLSeries_entire`). Later (2026-11-05): convexity bound (`HeckeConvex.tauL_convexity`), all nontrivial zeros in 11/2 ≤ Re s ≤ 13/2 (`HeckeZeros.tauL_zeros_in_strip`), τ(n) = Ω(n^{11/2}) (`TauOmega.tau_omega`), and Rankin–Selberg with error O(N^{3/5}) (`RankinExact.rankinSelberg_exact`).

## Summary

| Question | Verdict | Exact missing piece |
|---|---|---|
| mod-691 congruence | **proved, unconditional** | — (none; `τ ∈ ℤ` now proved via `key_dvd`) |
| general product bridge | **proved** | — (`qExpansion_discriminant_coeff`) |
| multiplicativity | **proved** | — (`tau_mul_coprime`, via constructed `T_p`) |
| Euler product of `L(Δ,s)` | **proved** (`Re s > 13/2`) | — (`HeckeZeros.tauL_eulerProduct`, via Rankin's absolute convergence `HeckeConvex.LSeriesSummable_tau_of_gt_13_2`; earlier `LSeries_tau_eulerProduct` for `Re s > 7`) |
| sub-Hecke bound | **proved**, `O(n^{23/4+ε})` (Weil) | — (`StepanovAS.tau_isBigO_23_4_unconditional`) |
| Deligne / Lehmer | open here | the Weil conjectures / an open problem (Lehmer proved for `n < 214,928,639,999`) |

Every question on the `τ` arc is now proved and axiom-clean, except Deligne's bound and Lehmer's conjecture.
