# The Andrews–Dragonette exact formula: what the repo's circle method can and cannot reach

Target (Andrews 1966 conjecture; Bringmann–Ono, Invent. Math. 165 (2006)):

  `α(n) = Σ_{k≥1} (−1)^{⌊(k+1)/2⌋} A_{2k}(n − k(1+(−1)^k)/4) M_{2k}(n)`,
  `M_{2k}(n) = π(24n−1)^{−1/4} I_{1/2}(π√(24n−1)/(12k))/k`,

with `n` fixed and the partial sum `adPartial n N` over `k ≤ N`, as `N → ∞`.
Directory: `RamanujanTau/AndrewsDragonette/`. Andrews' printed sum is `adPartial n ⌊√n⌋`
(`andrewsPrinted_eq_adPartial`, `rfl`).

## Summary

- **The exact formula is out of reach of the repo's inequality-only route.** This is a structural fact, not
  a matter of constants. There are two independent obstructions; both are documented below and checked
  numerically, and the first is partly formalized.
- **What is formalized** (axiom-clean):
  1. Convergence of the series for each `n`, conditional on one named hypothesis: Kloosterman cancellation
     in the modulus aspect, `HKS n θ C` with `θ < 1/2`. The trivial instance `θ = 1` is proved, so the
     hypothesis is exactly a power saving beyond square-root cancellation.
  2. An unconditional theorem showing that no pointwise cusp bound with `D < 0` exists:
     `¬ Hb C D` for every `D < 0`.
- **Not formalized:** that the limit equals `α(n)`.

## Step 1: analysis

### (A) The circle method with absolute-value bounds cannot converge as N → ∞

Rademacher's proof for `p(n)` uses the Farey dissection of order `N` on `Im τ = 1/N²`, with `z = K(y − iφ)`,
`K/N² ≤ |z| ≤ √2/N`, arcs of length `≤ 2/(KN)` and `φ(K)` arcs at level `K`. A pointwise bound
`‖non-principal part‖ ≤ C|z|^{−D}` therefore yields an aggregate error

  `Σ_{K≤N} φ(K) · C|z|^{−D} · 2/(KN) ≍ N^{2D−1} Σ_{K≤N} K^{−D} ≍ N^{D}`   (`0 ≤ D < 1`; `N^{2D−1}log N` at `D = 1`),

and `≍ N^{D}` for `D < 0`, using `|z| ≤ √2/N`.

- For `p(n)`, the remainder `|z|^{1/2}|F(q') − 1|` is effectively `D = −1/2`. The error is `O(N^{−1/2}) → 0`,
  and this is Rademacher's exactness.
- For `f`, the bound needed is `D < 0`, i.e. a non-principal part `f − ε_K b` that tends to 0 at the cusps.
  **That is false** (`not_Hb_of_neg`, Lean, axiom-clean): at `0/1` we have `ε_1 = 0`, and for real
  `q = e^{−2πs} → 1⁻` every term of `f` is `≥ 0`, so `|f(q)| ≥ 1`. In fact `f(q) → 4/3` (numerically `f(0.9995) = 1.33326`).
- The repo's best bounds are `Hb(C, 3/2)` (`MockCusp.Hb_holds`) and now `Hb(C, 1)` (`MockCusp.HbSharp_holds`).
  They give aggregate errors `N² log N` and `N log N`. The truth, Mordell-integral size `|z|^{−1/2}` at
  tangential points, would give `N^{1/2}`. Even `D = 0` would give `O(1)`. **No admissible `D` gives `o(1)`.**
  Sharpening `MockCusp` (to `D = 1/2 + ε` via the integrated denominator bound) improves Andrews' error term
  but cannot give exactness.
- Numerical confirmation (`numerics/remainder_L1.py`, `remainder_L1.txt`). The exact `L¹` mass of the
  non-principal part on the Farey line,
  `I(N) = ∫₀¹ |f(q) − ε_{K(x)} b(q)| dx`, `q = e^{2πi(x+i/N²)}`, `K(x)` = Farey denominator of the arc of `x`,
  is the quantity that `Andrews66.arc_bound` bounds:

  | N | 2 | 3 | 4 | 6 | 8 | 11 | 13 | 16 |
  |---|---|---|---|---|---|---|---|---|
  | I(N) | 1.53 | 1.63 | 1.97 | 2.09 | 2.49 | 2.82 | 3.02 | 3.39 |
  | I(N)/√N | 1.08 | 0.94 | 0.98 | 0.85 | 0.88 | 0.85 | 0.84 | 0.85 |

  So `I(N) ≈ 0.85√N`, matching `D = 1/2`. Meanwhile `∫(f − εb)e^{−2πinτ}dx` itself stays bounded and in fact
  tends to 0 (table B). Exactness lives entirely in **cancellation between the arc integrals of the Mordell
  parts**, which absolute values destroy.

### (B) Convergence of the series is itself a Kloosterman-cancellation theorem

`I_{1/2}(x) = √(2/(πx)) sinh x ≍ √x` as `x → 0`, so the `k`-th term is `≍ A_{2k}(·)/k^{3/2}`. In Lean this is
`k·M_{2k}(n) = A√k sinh(B/k)`, with bounds `w_le` and `w_sub_le`.

- Trivially `|A_{2k}| ≤ 2k`, which gives terms `O(k^{−1/2})`.
- Weil's bound gives `O(k^{−1+ε})`.
- Neither proves convergence. The series is **not absolutely convergent for any n** (Ahlgren–Dunn 2019,
  Thm 1.2). Numerically `Σ_{k≤N}|term|` grows like `0.45 log N` (`partial_sums.txt`, "abs").
- By Abel summation, convergence follows from (and is essentially equivalent to)
  `S(X) = Σ_{k≤X} (−1)^{⌊(k+1)/2⌋}A_{2k}(n_k)/k = O(X^{θ})` with `θ < 1/2`. This is a power saving beyond
  Weil in the *modulus* aspect, which needs spectral theory: Kuznetsov / Proskurin for half-integral weight,
  Goldfeld–Sarnak type.
- Ahlgren–Dunn, Thm 7.1: `Σ_{c≤X, 2|c} S(0,n,c,ψ)/c ≪ (n^{13/56+ε}X^{3δ/4} + n^{143/588+ε} + X^{1/2−δ})X^{ε}`.
  Bringmann–Ono obtained convergence through harmonic Maass forms (Zwegers' completion).

**Conclusion of Step 1.** Exactness for fixed `n` needs two inputs that the inequality-only method does not
have:
1. (B) Cancellation in sums of half-integral-weight Kloosterman sums over the modulus. This alone gives
   convergence.
2. (A) An *exact*, not inequality, treatment of the non-principal (Mordell/Zwegers) part on the arcs, whose
   arc integrals must be summed with cancellation. Equivalently, the Bringmann–Ono route: identify the
   completed `f` with a Maass–Poincaré series.

   My reading of Bringmann–Ono: the final identification also uses the fact that a weight-1/2 form with no
   principal parts vanishes, a Serre–Stark-type input. This is level 3 and unverified. In the Rademacher
   case that step is automatic, because the circle-method error tends to 0.

Neither input is formalized anywhere in the repo. Mathlib has no Weil bound for Kloosterman sums, let alone
Kuznetsov.

## Step 2: what is formalized (Lean, axiom-clean)

`#print axioms` (`AndrewsDragonette/Axioms.lean`) gives `[propext, Classical.choice, Quot.sound]` for every
theorem below. There is no `sorry`, no `native_decide` and no new axiom.

```lean
def AndrewsDragonette.adCoef (n k : ℕ) : ℂ := (-1 : ℂ) ^ ((k + 1) / 2) * Andrews66.AAnd (2 * k) (Andrews66.shiftA k n)
def AndrewsDragonette.adPartial (n N : ℕ) : ℂ := ∑ k ∈ Icc 1 N, adCoef n k * (Andrews66.MK (2 * k) n : ℂ)
def AndrewsDragonette.KSum (n X : ℕ) : ℂ := ∑ k ∈ Icc 1 X, adCoef n k / k
/-- named hypothesis: Kloosterman cancellation in the modulus aspect -/
def AndrewsDragonette.HKS (n : ℕ) (θ C : ℝ) : Prop := ∀ X : ℕ, 1 ≤ X → ‖KSum n X‖ ≤ C * (X : ℝ) ^ θ

theorem AndrewsDragonette.adPartial_converges_of_HKS {n : ℕ} (hn : 1 ≤ n) {θ C : ℝ} (hθ : θ < 1 / 2)
    (hK : HKS n θ C) : ∃ L : ℂ, Tendsto (fun N => adPartial n N) atTop (𝓝 L)
theorem AndrewsDragonette.HKS_trivial (n : ℕ) : HKS n 1 2
theorem AndrewsDragonette.andrewsPrinted_eq_adPartial (n : ℕ) :
    Andrews66.andrewsPrinted n = adPartial n (Nat.sqrt n)
theorem AndrewsDragonette.not_Hb_of_neg {C D : ℝ} (hD : D < 0) : ¬ Andrews66.Hb C D
theorem AndrewsDragonette.one_le_fA_real {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) :
    1 ≤ ‖MockTheta3.Radial.fA (t : ℂ)‖
```

| file | content |
|---|---|
| `Abel.lean` | `abel_identity` (summation by parts), `tendsto_of_abel` (convergence from a summable Abel remainder and vanishing boundary term) |
| `Weight.lean` | `wt A B x = A√x sinh(B/x)`; `sinh_lip`; `w_le`: `\|w(x)\| ≤ AB cosh B · x^{−1/2}`; `w_sub_le`: `\|w(x+1)−w(x)\| ≤ 2AB cosh B · x^{−3/2}` |
| `Main.lean` | `adCoef`, `adTerm`, `adPartial`, `KSum`, **`HKS`**, `KSum_trivial`, `HKS_trivial`, `k_MK` (`k·M_{2k}(n) = w(k)`), **`adPartial_converges_of_HKS`** |
| `Obstruction.lean` | `one_le_fA_real`, `qp_zero_one_real`, **`not_Hb_of_neg`** |
| `numerics/partial_sums.py`, `.txt` | partial sums to `N = 8000` for `n ∈ {1,2,3,5,10,20,50,100}` |
| `numerics/remainder_L1.py`, `.txt` | `I(N)`, table above |

The hypothesis is not circular. `HKS` is a statement about finite Kloosterman sums only; it mentions neither
`α(n)` nor the Bessel weights. The convergence theorem is a real Abel-summation argument against the proved
weight bounds. The proof does not need `C` to be uniform in `n`.

## Numerical evidence (level 4)

### Table B: fixed n, N → ∞ (`numerics/partial_sums.txt`, double precision, exact `α(n)`)

The entries are `adPartial n N − α(n)`.

| N | n=1 | n=2 | n=3 | n=5 | n=10 | n=20 | n=50 | n=100 |
|---|---|---|---|---|---|---|---|---|
| 10 | +0.031 | +0.107 | −0.286 | −0.079 | +0.028 | +0.137 | +0.176 | −0.182 |
| 100 | −0.008 | +0.080 | −0.121 | +0.046 | −0.036 | +0.082 | +0.015 | −0.010 |
| 1000 | −0.0014 | +0.019 | −0.024 | −0.015 | −0.028 | +0.013 | +0.013 | +0.004 |
| 8000 | −0.0032 | +0.0012 | +0.0060 | +0.0044 | −0.0042 | +0.0010 | −0.0050 | +0.0025 |

- The partial sums converge, slowly and with oscillation (roughly `N^{−1/2}`), to the exact `α(n)`. This is
  consistent with Bringmann–Ono.
- `|S(X)|/√X` decreases, and `|S(X)|` stays `O(1)`–`O(2)` up to `X = 8000` (n = 10: `|S| ≈ 1.8` at
  `X = 100` and `X = 8000`). This is consistent with `HKS` for a small `θ`, and far below the threshold 1/2.
- `Σ|term|` grows logarithmically, consistent with non-absolute convergence.

## Evidence levels

1. **Lean, axiom-clean:**
   - `adPartial_converges_of_HKS` (conditional only through the hypothesis argument `HKS`)
   - `HKS_trivial`, `tendsto_of_abel`, `w_le`, `w_sub_le`, `k_MK`
   - `not_Hb_of_neg`, `one_le_fA_real`
2. **Lean, conditional on a named hypothesis:** convergence of the Andrews–Dragonette series, given
   `HKS n θ C` with `θ < 1/2`.
3. **Paper only:**
   - The aggregate `N^{D}` computation in (A), and the claim that no inequality-only bound reaches `o(1)`.
   - The truth of `HKS`. This should follow from Ahlgren–Dunn Thm 7.1; the match of normalizations (their
     `S(0,n,c,ψ)` on Γ₀(2) against `(−1)^k A_b(k,n)`, via `Andrews66.Ab_printed`) is not checked.
   - Exactness (Bringmann–Ono).
4. **Numerical:** tables A and B.

## What it would take to finish

- **HKS.** Kuznetsov / Proskurin for weight 1/2 with the `η`-type multiplier on Γ₀(2), plus a spectral
  large-sieve or Weyl-law input. This is a large analytic-number-theory formalization, many thousands of
  lines and probably months. Even Weil's bound (algebraic geometry over finite fields) is absent from Mathlib,
  though it would not suffice anyway.
- **Exactness.** Either harmonic Maass forms and Poincaré series of weight 1/2 (Bringmann–Ono), or an exact
  arc-by-arc treatment of the Mordell integrals with the resulting Kloosterman–Bessel sums controlled
  spectrally. Either way it needs Zwegers' completion formalized at every cusp. Estimate: a multi-month
  project.
- A cheaper partial target, not attempted here: under `HKS` with `C` polynomial in `n`, plus the sharp Andrews
  bound, `|α(n) − L(n)|` is bounded by `A₁√n log n` plus the tail. This does not give `α(n) = L(n)`. The proved
  weight bound `w_le` uses `cosh B`, which is far too lossy for `k ≤ √n`, so it would also need a refined
  weight bound for `B/k ≥ 1`.

## Literature

- G. E. Andrews, *Amer. J. Math.* 88 (1966) 454–490 (the conjecture and the `O(√n log n)` asymptotic).
- K. Bringmann, K. Ono, *The f(q) mock theta function conjecture and partition ranks*, Invent. Math. 165 (2006).
- S. Ahlgren, A. Dunn, *Maass forms and the mock theta function f(q)*, Math. Ann. (2019), arXiv:1806.01187:
  Thm 1.1 (error `n^{−1/147+ε}` at `N = γ√n`), Thm 1.2 (no absolute convergence), Thm 7.1 (Kloosterman bound).
- S. Zwegers, *Mock theta functions*, thesis (2002).
