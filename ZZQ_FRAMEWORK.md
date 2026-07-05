# The `ℤ((q))` bilateral-theta framework — design & roadmap

> **STATUS (2026-07): the headline goal — the pentagonal number theorem — is now PROVED, by a different
> route.** Rather than land in `ℤ((q))` to evaluate at the non-unit `z = −q`, the proof
> (`MockTheta5EulerPentagonal.lean`) builds a *shifted base-`q³`* bilateral Jacobi triple product and
> evaluates at `z = −1` (a **unit** in `PowerSeries ℤ`), sidestepping the non-unit obstruction entirely.
> So `evalZ` / Piece 1 stands as built, but Piece 2 (the `ℤ((q))` flatten) was **not needed** for
> pentagonal. See the README and `euler_pentagonal`, `jacobi_cube_identity`, `five_dvd_coeff_partitionGF`.
> The document below is retained as the original design record.

Goal: evaluate the repo's formal-`z` Jacobi triple product at **non-unit** `z` (= `±q`, `−q²`, …) to close
the famous *product* identities (pentagonal number theorem, both Rogers–Ramanujan products, Identity A's
theta form). Blocked in `PowerSeries ℤ` because the bilateral form needs `z⁻¹`, so `z` must be a unit, and
`±q`/`−q²` are non-units there. Fix: land in `ℤ((q)) = LaurentSeries ℤ`, where `q = X` is a unit.

## Piece 1 — the non-unit evaluation primitive `evalZ`  ✅ DONE (`MockTheta5LaurentEval.lean`, `e605259`)
`evalZ a : ℤ[z;z⁻¹] →+* ℤ((q))`, `z ↦ qᵃ` (`evalZ_T : z ↦ q^{aⁿ}`), a genuine ring hom because `qᵃ` is a unit
in `ℤ((q))` (`uSingle`). This is the evaluation impossible into `PowerSeries ℤ`. (For `z = c·qᵃ` with a sign
`c ∈ ℤˣ`, generalize `uSingle` to `single a c`; `−q` needs `single 1 (−1)`.)

## Piece 2 — the grading-addition flatten  ⬜ REMAINING (custom `HahnSeries.SummableFamily`)
Turn an identity `A = B` in `PowerSeries (LaurentPolynomial ℤ)` (outer `q`, inner `z`) into `ℤ((q))`:
apply `PowerSeries.map (evalZ a)` (clean ring hom) → `PowerSeries (ℤ((q)))`, then **substitute outer `q ↦ X`**,
collapsing to `ℤ((q))`. That is `hsum` of the family `n ↦ (coeff n ·) · Xⁿ` in `ℤ((q))`, summable when
`ord + n → ∞`.
- Why not Mathlib's `heval`/`powerSeriesFamily`: they substitute a power series at a positive-order Hahn
  element but **keep the two gradings separate** (result lands in `HahnSeries Γ (ℤ((q)))`, a fresh `Γ`), not
  the `z,q` grading-*addition* needed here.
- Build: a `SummableFamily ℤ ℤ ℕ` `n ↦ (evalZ a (coeffₙ)) * single n 1`; prove `isPWO` of `⋃ supports` +
  finite fibers (holds because coefficient orders grow `≥ −a·(z-degree)` and `z-degree = O(n)`, so
  `ord + n → ∞`); then `hsum`, with `SummableFamily.hsum_mul` giving multiplicativity so it's a ring hom on
  the relevant subring (⟹ `flatten(qfac2InfL·SZ·SZinv) = ∏ flatten(factor)`).

## Piece 3 — the triangular JTP  ⬜ REMAINING (from `qbinom`, base `q`)
`Σ_{n∈ℤ} zⁿ q^{n(n-1)/2} = ∏_{k≥1}(1−qᵏ)(1+z qᵏ⁻¹)(1+z⁻¹ qᵏ)`, built from `qbinom` (`∏(1+tqⁱ)=Σ q^{C(k,2)}[n,k]tᵏ`)
the way `classical_jacobi_triple_product` is built from `finite_jtp` — but at **base `q`** (all powers), not
`q²` (odd powers). Needed because the `n²`-form JTP only reaches thetas `Σ q^{k n² + a n}` with **integer** `k`.

## Reachability (once Pieces 2, 3 land)
| target theta | form | route |
|---|---|---|
| Identity A: `Σ(−1)ⁿq^{2n²+n}` | `k=2` (integer) | `n²`-JTP `∘ E₂ ∘ evalZ(z=−q) ∘` flatten — needs only **Piece 2** |
| pentagonal: `Σ(−1)ⁿq^{(3n²−n)/2}` | base `q³` triangular | triangular-JTP `∘ E₃ ∘ evalZ(z=−q) ∘` flatten — needs **2 + 3** |
| RR1: `Σ(−1)ⁿq^{(5n²−n)/2}` | base `q⁵`, `z=−q²` | triangular-JTP `∘ E₅ ∘ evalZ(z=−q²) ∘` flatten — **2 + 3** |
| RR2 | base `q⁵` | as RR1 with the other residue |

Identity A's product form is already proved independently via Euler (`identityA_product`); Piece 2 alone would
give its bilateral-theta form as a second route and the first end-to-end demonstration of the framework.
Pieces 2 + 3 close pentagonal and both Rogers–Ramanujan **products**.
