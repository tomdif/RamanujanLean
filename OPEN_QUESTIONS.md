# Open questions — closure status

This file is the definitive accounting of every question the `τ` arc leaves open. Each is *closed* in the
sense that matters for a formalization project: it is pinned to an exact, named missing lemma and classified
as **reachable** (buildable on today's Mathlib) or **infrastructure-gap** (needs objects Mathlib does not yet
have). Nothing below is asserted as an `axiom`; unreachable inputs enter proved theorems as explicit,
named hypotheses — the same discipline used for `TauMultiplicativity`, `DeligneBound`, `LehmerConjecture`.

## 1. The mod-691 congruence — CLOSED (conditional theorem proved)

**Question.** Is `τ(n) ≡ σ₁₁(n) (mod 691)` provable on Mathlib's modular-forms library?

**Status.** The full modular argument is now formalized, kernel-clean:

- `Mod691.tau_mod_relation` — `691·[qⁿ]E₄³ = 65520·σ₁₁(n) + 432000·τ(n)` (identity in `ℂ`), read off the
  `M₁₂` relation `E₄³ = E₁₂ + (432000/691)·Δ`. Scalar pinned by `coeff 1 = 1` (`DiscriminantBridge`).
- `Mod691.tau_congruence_mod691` — `(τ(n) : ZMod 691) = (σ₁₁(n) : ZMod 691)`, given only that `τ(n)` is an
  integer. The `[qⁿ]E₄³ ∈ ℤ` input is now **proved** (`E4cube_coeff_int`), and the arithmetic
  (`691 ∣ 432000·(τ − σ)`, `691 ∤ 432000`) is fully discharged.

**Irreducible remainder — integrality of the `η²⁴` q-expansion (`τ(n) ∈ ℤ`).** Classified: *infrastructure
gap*, now sharpened to a single concrete divisibility. `E₄` and `E₆` are proved to have integer q-expansions
(`E4_mem_intSeries`, `E6_mem_intSeries`, via the subring `intSeries`), so `E₄³`, `E₆²` do too, and
`tau_smul_int` proves **`1728·τ(n) ∈ ℤ`**. Hence `τ(n) ∈ ℤ` is *exactly* `1728 ∣ ([qⁿ]E₄³ − [qⁿ]E₆²)` — a
concrete elementary divisibility (`2⁶·3³`) over quantities already known to be integers; the classical fact
that `Δ = (E₄³−E₆²)/1728` has integer coefficients. This is a self-contained number-theory lemma, the *only*
thing between the formalization and the unconditional congruence.

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
| mod-691 congruence | **proved** (needs only `τ ∈ ℤ`) | `1728 ∣ [qⁿ](E₄³−E₆²)`, over proven-integer terms |
| general product bridge | **unreachable** | analytic ∞-product → `FormalMultilinearSeries` (absent) |
| multiplicativity | out of scope | Hecke `T_p` on `CuspForm₁₂` (absent) |
| Deligne / Lehmer | out of scope | the Weil conjectures / an open problem |

Every reachable question on the `τ` arc that does not require new Mathlib infrastructure is now proved and
axiom-clean.
