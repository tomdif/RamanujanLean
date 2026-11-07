# GORZ Theorem 2, `d = 3`, for the Riemann Ξ-function (Dimitrov–Lucas): reduction and status

Normalizations follow `docs/GORZ_XI.md` and `docs/GORZ_XI_EFFECTIVE.md`. Here `γ = gammaMathlib`, defined by
`(−1+4z²)Λ(1/2+z) = Σ γ(n) z^{2n}/n!`, and `J^{3,n}_γ = jensenSeq gammaMathlib 3 n
= γ(n) + 3γ(n+1)X + 3γ(n+2)X² + γ(n+3)X³`.

Target: `J^{3,n}_γ` is hyperbolic for every `n ≥ 0`. This is Dimitrov–Lucas, *Higher order Turán inequalities
for the Riemann ξ-function*, Proc. AMS 139 (2011) 1013–1022.

## Result

| Statement | Lean name | Level |
|---|---|---|
| A real cubic `d+cX+bX²+aX³` with `a > 0` and `Disc = 18abcd−4b³d+b²c²−4ac³−27a²d² ≥ 0` is hyperbolic | **`hyperbolic_cubic`** | **(1)** |
| `Disc(J^{3,n}_α) = 27·hot α n`, where `hot α n = 4(α₁²−α₀α₂)(α₂²−α₁α₃) − (α₁α₂−α₀α₃)²` (indices `n+j`) | `disc_jensen3` | (1) |
| Any real sequence: `α(n+3) > 0` and `hot α n ≥ 0` ⇒ `J^{3,n}_α` hyperbolic | **`jensen3_of_hot`** | **(1)** |
| HOT is a Lipschitz condition: for positive `α` with Turán defects `A = tdef α n > 0` and `B = tdef α (n+1) > 0`, `hot α n ≥ 0 ⟺ \|B^{−1/2} − A^{−1/2}\| ≤ 1` | **`hot_nonneg_iff_lip`** (with `hot_eq`) | **(1)** |
| `γ(n) > 0` for all `n` | `gamma_pos` | (1) |
| `hot γ n ≥ 0` ⇒ `J^{3,n}_γ` hyperbolic | `jensen3_gamma_of_hot` | (1) |
| **`J^{3,n}_γ` hyperbolic for every `n ≥ 0`** | **`jensen3_gamma`** | **(2)**, hypothesis `DLHyp` only |
| Dimitrov–Lucas HOT for `Ξ`, all `n` | `hot_gamma` | (2), `DLHyp` |
| `DLHyp ⟺ ∀ n, γ(n)γ(n+2) < γ(n+1)² ∧ hot γ n ≥ 0` | **`dlHyp_iff`** | (1) |
| Sufficient split: defect `> 0`, nonincreasing, and `a_n ≤ a_{n+1}(1+√a_n)²` ⇒ `DLHyp` | `dlHyp_of_mono` | (1) |
| `DLHyp` itself | `DLHyp` (`def … : Prop`) | (3) Dimitrov–Lucas 2011, method **not verified** (see below); (4) numerics, `n ≤ 10⁴` |

Running `#print axioms` on every name above gives `[propext, Classical.choice, Quot.sound]` (see `Main.lean`).
The files contain no `sorry`, no `axiom` and no `native_decide`.

```lean
noncomputable def GORZXiD3.tdef (α : ℕ → ℝ) (n : ℕ) : ℝ := 1 - α n * α (n + 2) / α (n + 1) ^ 2
noncomputable def GORZXiD3.lam (α : ℕ → ℝ) (n : ℕ) : ℝ := 1 / Real.sqrt (tdef α n)
def GORZXiD3.DLHyp : Prop :=
  ∀ n : ℕ, 0 < tdef gammaMathlib n ∧ |lam gammaMathlib (n + 1) - lam gammaMathlib n| ≤ 1
theorem GORZXiD3.jensen3_gamma (h : DLHyp) (n : ℕ) : Hyperbolic (jensenSeq gammaMathlib 3 n)
theorem GORZXiD3.dlHyp_iff : DLHyp ↔ ∀ n : ℕ,
    gammaMathlib n * gammaMathlib (n + 2) < gammaMathlib (n + 1) ^ 2 ∧ 0 ≤ hot gammaMathlib n
theorem GORZXiD3.jensen3_of_hot {α : ℕ → ℝ} {n : ℕ} (hpos : 0 < α (n + 3)) (hH : 0 ≤ hot α n) :
    Hyperbolic (jensenSeq α 3 n)
theorem GORZXiD3.hyperbolic_cubic {a b c d : ℝ} (ha : 0 < a)
    (hD : 0 ≤ 18*a*b*c*d - 4*b^3*d + b^2*c^2 - 4*a*c^3 - 27*a^2*d^2) :
    Hyperbolic (C d + C c * X + C b * X ^ 2 + C a * X ^ 3)
```

**What the conditional theorem does and does not give.** `dlHyp_iff` shows that `DLHyp` is exactly the
statement "strict Turán and higher-order Turán for all `n`". The Lean part is therefore the full *algebraic*
reduction: hyperbolicity of the cubic, the exact normalization (`Disc = 27·HOT` in GORZ's normalization, which is
also Dimitrov–Lucas's form of the inequality), and the Lipschitz reformulation. The *analytic* content of
Dimitrov–Lucas, a proof of HOT for the actual `γ(n)`, is **not** formalized. Unlike `CVHyp` in the `d = 2`
case, `DLHyp` is not a pointwise property of the kernel `Φ`. It is a statement about the moment sequence.

## Derivations

1. **Discriminant.** `J^{3,n}` has coefficients `(a,b,c,d) = (γ₃, 3γ₂, 3γ₁, γ₀)`. Then
   `18abcd−4b³d+b²c²−4ac³−27a²d² = 27[3γ₁²γ₂² − 4γ₁³γ₃ − 4γ₀γ₂³ + 6γ₀γ₁γ₂γ₃ − γ₀²γ₃²]`
   `= 27[4(γ₁²−γ₀γ₂)(γ₂²−γ₁γ₃) − (γ₁γ₂−γ₀γ₃)²]`. This is DL's inequality at centre `n+1`, with no rescaling. HOT is
   invariant under `γ(n) ↦ Cλⁿγ(n)`, so the same inequality holds for `x_n = M_n/Γ(n+½)`, where
   `M_n = ∫_0^∞ t^n Φ(√t) t^{−1/2} dt = 2b_{2n}`.
2. **Cubic ⇒ hyperbolic.**
   * The IVT on `[−M, M]` with `M = 1 + (|b|+|c|+|d|)/a` gives a real root `r`.
   * The cubic factors as `P = (X−r)Q` with `Q = aX² + (b+ar)X + (c+br+ar²)`.
   * Once `d = −(cr+br²+ar³)`, the identity `Disc P = Disc Q · Q(r)²` holds by `ring`, and `Q(r) = P'(r)`.
   * If `Q(r) ≠ 0`, then `Disc Q ≥ 0`. If `Q(r) = 0`, then `Disc Q = (b+3ar)² ≥ 0`.
   * Finally `GORZXiEff.hyperbolic_quadratic` and `roots_mul` finish the proof.
3. **Lipschitz form.** Let `A = tdef n` and `B = tdef (n+1)`. Then `γ₀γ₃/(γ₁γ₂) = (1−A)(1−B)`, so
   `hot = γ₁²γ₂²(4AB − (A+B−AB)²)`. With `s = √A` and `t = √B`:
   `4s²t² − (s²+t²−s²t²)² = (s²t² − (s−t)²)(2st + 1 − (1−s²)(1−t²))`.
   The second factor is `> 0` because `0 < A, B < 1`. So `hot ≥ 0 ⟺ |s−t| ≤ st ⟺ |1/t − 1/s| ≤ 1`.

## Numerical evidence (level 4)

The script is `scripts/gorzxi_d3/hot_numerics.py N dps deg`. It computes `γ(n) = 32·n!/(2n)!·∫_0^7 u^{2n}Φ(u)du`.
Here `Φ` is truncated at 9 theta terms and integrated by composite Gauss–Legendre (140 panels). All moments share
one evaluation of `Φ`.

* The script reproduces GORZ's `γ(10) = 1.63233804903e−17` and `γ(100) = 6.57772637858e−205`.
* Two runs at `N = 3000`, 80 digits, with node degrees 40 and 56, agree to relative error `2.3e−65` for all `n`.
* **HOT holds for `1 ≤ m ≤ 3000`, with 0 failures.** `Q_m = (γ_mγ_{m+1}−γ_{m−1}γ_{m+2})²/(4(γ_m²−γ_{m−1}γ_{m+1})(γ_{m+1}²−γ_mγ_{m+2}))`
  takes the values 0.9435 (m=1), 0.9733 (10), 0.99488 (100), 0.99934 (1000), 0.99976 (3000). In this form the
  margin `1 − Q_m ≈ a_m` is thin and decays like `1/m`. That margin comes from the strict Turán inequality.
* **In the Lipschitz form the margin is large.** On `0 ≤ n ≤ 3000`:
  * the increments `Λ_{n+1} − Λ_n` (`Λ = a^{−1/2}`) lie in `[0.0103, 0.326]`, against the allowed `[−1, 1]`;
  * the maximum, 0.326, is at `n = 0`;
  * `Λ` is strictly increasing, so the defect `a_n` is strictly decreasing, and `√(n+1)·ΔΛ_n ≈ 0.33 → 0.58`;
  * the Turán defect satisfies `a_n > 0` throughout, with `(n+1)a_n` increasing from 0.0696 (n=0) to 0.66 (n=1000).

  So both sides of `DLHyp` hold numerically, and so do the hypotheses of `dlHyp_of_mono`. The hypothesis is not
  vacuous. It is a nontrivial true-looking statement, consistent with the unconditional `n → ∞` asymptotics
  below.
* **Run at `N = 10⁴`, 60 digits.** HOT holds for `1 ≤ m ≤ 10⁴` with 0 failures (`Q_{10⁴} = 0.9999255`). The
  increments `ΔΛ_n` lie in `[0.00557, 0.326]` and are all positive, so `Λ` is strictly increasing on
  `0 ≤ n ≤ 10⁴`. The minimal Turán defect is `a_{10⁴} = 7.45e−5 > 0`. The values agree with the `N = 3000` run.

**Heuristic asymptotics.** From `docs/GORZ_XI.md`, `−nΔ²log γ(n) → 1`, although slowly, and
`n^{3/2}Δ³log B(n) → 0` (`xiKernelHyp_holds`, level 1). Then `a_n ~ κ_n/n` with `κ_n → 1`, and
`ΔΛ_n ≈ Δc_n/(2c_n^{3/2}) + O(n^{−1/2}) → 0`. So `DLHyp` holds for all sufficiently large `n`, and only an
**effective** threshold plus a finite range is missing. That part is not formalized here. As noted in
`GORZ_XI_EFFECTIVE.md`, the GORZXi constants make the threshold astronomically large.

## Dimitrov–Lucas's method: what could and could not be checked (level 3)

The paper is not freely accessible from this machine: the AMS PDF returns 403, and the UNESP repository copy
returns 401. Abstract-level sources confirm the statement: the Maclaurin coefficients of ξ satisfy the
higher-order Turán inequalities, and therefore the degree-3 Jensen polynomials are hyperbolic, proved without
assuming RH.

I could **not** confirm the internal method. My unverified recollection is that it combines an asymptotic
analysis of the moments `b_m` of `Φ` with a direct computation for small `n`, rather than a single pointwise
kernel property like `CVHyp`. Nothing in the Lean code depends on this. If DL do use a pointwise kernel property,
the right next step is to state it as a named hypothesis and derive `DLHyp` from it.

Why no Chebyshev-type proof was attempted:
* For `d = 2`, Turán is equivalent to "`s_n = E_{μ_{n+1}}[G']` is increasing", where `G = −log Φ(√t)` and
  `μ_k ∝ t^{k−½}e^{−G}`. That follows from one covariance sign.
* HOT is equivalent to `(D₁s₂ − D₂s₀)² ≤ 4s₂D₁²D₂` with `D_i = s_i − s_{i−1}`. This is a quantitative,
  second-order condition: the relative variation of `D` must be `≲ 2√(D/s) ~ n^{−1/2}`. It does not reduce to the
  sign of a single covariance.

## Files (all new)

| File | Contents |
|---|---|
| `RamanujanTau/GORZXiD3/Cubic.lean` | `hyperbolic_mul`, `hyperbolic_X_sub_C`, `cubic_has_root`, **`hyperbolic_cubic`**, `jensenSeq_three`, `hot`, `disc_jensen3`, **`jensen3_of_hot`** |
| `RamanujanTau/GORZXiD3/Lipschitz.lean` | `tdef`, `lam`, `hot_eq`, `tdef_lt_one`, `bracket_factor`, `lip_iff`, **`hot_nonneg_iff_lip`**, `lip_of_mono` |
| `RamanujanTau/GORZXiD3/Main.lean` | `gamma_pos`, `jensen3_gamma_of_hot`, **`DLHyp`**, `hot_gamma`, **`jensen3_gamma`**, `tdef_pos_iff`, **`dlHyp_iff`**, `dlHyp_of_mono`, `#print axioms` |
| `scripts/gorzxi_d3/hot_numerics.py` | level-4 numerics (HOT `Q_m`, Turán defect, Lipschitz increments) |

Imports are `RamanujanTau.GORZXiEff.Turan2` and `RamanujanTau.GORZXiEff.Main`, both unmodified. To build, run one
process: `lake build RamanujanTau.GORZXiD3.Main` (about 20 s per module once `GORZXiEff` is built).

## What remains

1. **Discharge `DLHyp`.** There are two routes:
   * **Route (a): effective asymptotics.** Prove effective two-sided bounds on the Turán defect `a_n`, with
     relative accuracy `o(n^{−1/2})`, for `n ≥ N₀`, and certify `n < N₀` in the kernel. The large Lipschitz
     margin (`ΔΛ ≤ 0.33` against 1) means the finite range can tolerate relative errors in `γ(n)` of about `10⁻³`.
     The tail, however, needs genuinely sharp Laplace-type asymptotics of `∫u^{2n}Φ`, which is well beyond
     GORZXi's current constants.
   * **Route (b): a third-order kernel inequality.** Find a pointwise, `CVHyp`-like property of `Φ` that implies
     `a_n` nonincreasing and `a_n ≤ a_{n+1}(1+√a_n)²` (`dlHyp_of_mono`). No candidate is known to me. Reading DL's
     §2–3 should come first.
2. An unconditional "`DLHyp` holds for all large `n`" is within reach from `xiKernelHyp_holds` (k = 2, 3). It is
   not done here, because eventual hyperbolicity for `d = 3` is already the level-(1) result
   `GORZXi.xi_gorz_unconditional 3`.
