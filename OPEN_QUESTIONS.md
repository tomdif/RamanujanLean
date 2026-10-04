# Open questions — closure status

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

**Status. Proved, axiom-clean** (`DiscriminantQExpansion.qExpansion_discriminant_coeff`). The earlier verdict
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

## 3. `τ` multiplicativity — CLOSED (proved, 2026-10-04); Deligne / Lehmer — out of scope

- **Multiplicativity and the Hecke recurrence are proved** (`HeckeQExp.tau_mul_coprime`,
  `tau_hecke_recurrence`; axiom-clean). `HeckeCore`/`HeckeForm` build `T_p` on `CuspForm 𝒮ℒ k` by the
  elementary coset computation, without Mathlib's double-coset machinery. `HeckeQExp` computes its
  q-expansion, which gives a `HeckeData` term and an instance of `TauHeckeMaster`.
- `DeligneBound` **is** Deligne's proof of the Weil conjectures — out of reach.
- `LehmerConjecture` (`τ(n) ≠ 0`) is a famous open problem.

The last two are documented as hypotheses, not defects.

## Summary

| Question | Verdict | Exact missing piece |
|---|---|---|
| mod-691 congruence | **proved, unconditional** | — (none; `τ ∈ ℤ` now proved via `key_dvd`) |
| general product bridge | **proved** | — (`qExpansion_discriminant_coeff`) |
| multiplicativity | **proved** | — (`tau_mul_coprime`, via constructed `T_p`) |
| Deligne / Lehmer | out of scope | the Weil conjectures / an open problem |

Every reachable question on the `τ` arc that does not require new Mathlib infrastructure is now proved and
axiom-clean.
