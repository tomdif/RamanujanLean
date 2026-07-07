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

## 2. The general product bridge `[qⁿ]∏(1−qⁿ)²⁴ = τ(n)` — CLOSED (unreachable, precisely characterized)

**Question.** Can Mathlib's *analytic* `Δ = η²⁴` be identified coefficient-by-coefficient with the *formal*
Euler product `q·∏(1−qⁿ)²⁴` (connecting `τ_modular` to the repo's combinatorial `τ`)?

**Status.** *Infrastructure gap — not reachable on today's Mathlib.* Established concretely:

- The leading coefficients are done analytically (`DiscriminantBridge`: `coeff 0 = 0`, `coeff 1 = 1`).
- The general bridge needs to carry a *formal infinite product's* coefficients to an *analytic infinite
  product's* Taylor coefficients **in the metric topology**. `PowerSeries.eval₂` cannot do this: it requires
  `IsLinearTopology ℂ ℂ`, which is false for the analytic topology (`eval₂` is built for adic evaluation).
- The two tools that would close it are both absent from Mathlib: an *analytic-infinite-product →
  `FormalMultilinearSeries`* lemma, and a *polynomial → `FormalMultilinearSeries`* + tail-order estimate for
  the truncation route. Either is a substantial analytics contribution.

This is why the combinatorial-`τ` congruences in the repo (`Congruences/*`) are certified on finite ranges as
named hypothesis classes rather than derived from the modular side: the bridge that would unify them is this
missing object.

## 3. `τ` multiplicativity / Deligne bound / Lehmer — unchanged (out of scope)

- `TauMultiplicativity` reduces to constructing Hecke operators `T_p` on `CuspForm₁₂` — the one genuinely
  Mathlib-absent piece of the Hecke story (`HeckeOperator.HeckeData`).
- `DeligneBound` **is** Deligne's proof of the Weil conjectures — out of reach.
- `LehmerConjecture` (`τ(n) ≠ 0`) is a famous open problem.

These are documented as hypotheses, not defects.

## Summary

| Question | Verdict | Exact missing piece |
|---|---|---|
| mod-691 congruence | **proved, unconditional** | — (none; `τ ∈ ℤ` now proved via `key_dvd`) |
| general product bridge | **unreachable** | analytic ∞-product → `FormalMultilinearSeries` (absent) |
| multiplicativity | out of scope | Hecke `T_p` on `CuspForm₁₂` (absent) |
| Deligne / Lehmer | out of scope | the Weil conjectures / an open problem |

Every reachable question on the `τ` arc that does not require new Mathlib infrastructure is now proved and
axiom-clean.
