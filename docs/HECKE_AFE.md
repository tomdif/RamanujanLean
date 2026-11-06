# Smoothed approximate functional equation for L(Δ, s)

Module: `RamanujanTau/HeckeAFE/` (entry point `Main.lean`).
Build: `nice -n 10 lake build RamanujanTau.HeckeAFE.Main` (exit 0, 2026-11-06). Every headline
prints `[propext, Classical.choice, Quot.sound]`. There is no `sorry`, no `axiom` and no
`native_decide`. Six files, 1342 lines.

This is milestone (1) of `HAFNER_PROPORTION.md` §4: an approximate functional equation for
L(Δ, 6+it) that is uniform in t and carries the exact Γ-ratio phase.

## Evidence levels

| result | level |
|---|---|
| exact smoothed AFE for Λ, every s ∈ ℂ, every X > 0 (`heckeLambda_afe`) | **(1) Lean, axiom-clean** |
| Dirichlet expansion and the normalized AFE for L, 5 < Re s < 7 (`tauL_afe`, `tauL_afe_line`) | **(1)** |
| \|ε(6+it)\| = 1 (`norm_eps_line`) | **(1)** |
| uniform weight bounds V_decay / V_sub_one / V_bound (uniform in t ∈ ℝ, ξ > 0) | **(1)** |
| truncated AFE, one length or two, error O((1+\|t\|)^{−B}) (`tauL_afe_truncated*`) | **(1)** |
| pointwise \|L(6+it)\| ≤ \|S₁\| + \|S₂\| + C(1+\|t\|)^{−B} (`norm_tauL_le_afe`) | **(1)** |
| `SCS2 η B`, the two-sided shifted-convolution hypothesis | statement only (Lean `def`, not used) |
| AFE numerically correct to about 10⁻¹¹ (truncation-limited), \|ε\| = 1 to 10⁻⁴¹ | (4) PARI, `scripts/hecke_afe/afe_check.gp` |
| the AFE diagonal grows with slope 2c = `cDelta`, matching `CriticalMeanSquareAsymp` | (4) PARI, `scripts/hecke_afe/ms_check.gp` |
| twisted second moment ∫\|L\|²(h/k)^{it}, i.e. Goal 2 | (3) plan only, §5 |

## 1. Formulation (the cheapest rigorous one)

**Notation.**

* G(u) = e^{u²}.
* Line integrals are written with dy: (1/2πi)∫_{(c)} f(u) du = (1/2π)∫_ℝ f(c+iy) dy. In Lean this
  is `vline f c / (2π)`.
* Λ(s) = (2π)^{−s}Γ(s)L(Δ,s), the function `heckeLambda`. Hecke: Λ(12−s) = Λ(s), Λ is entire
  and bounded on vertical strips.

**Definitions** (Lean names in brackets):

    I_Λ(s; X)  = (1/2πi)∫_{(c)} Λ(s+u) X^u e^{u²} du/u                       [ILam s X c]
    W_s(ξ)     = (1/2πi)∫_{(c)} Γ(s+u) ξ^{−u} e^{u²} du/u                      [WGam s ξ c]
    V_s(ξ)     = W_s(ξ)/Γ(s)          (with c = 2)                              [V s ξ]
    ε(s)       = (2π)^{2s−12} Γ(12−s)/Γ(s)                                     [eps s]

On the line, V_{6+it}(ξ) = (1/2πi)∫_{(2)} [Γ(6+it+u)/Γ(6+it)] ξ^{−u} e^{u²} du/u, which is the brief's
weight with G(u) = e^{u²}. Also ε(6+it) = (2π)^{2it}Γ(6−it)/Γ(6+it).

**Why this formulation is cheap.**

* The AFE is an exact identity. There is no O(t^{−A}) error and no Stirling inside the identity.
* Stirling enters only through the two-sided bounds already in `Stirling.Absolute`, and only to
  bound the weights.
* The contour machinery is generic, about 300 lines:
  * Cauchy on rectangles, then height → ∞ (`vline_shift`);
  * one explicit integral, ∫_ℝ e^{(b+iy)²}/(b+iy) dy = π, done by Fubini with
    1/u = ∫_0^∞ e^{−ux}dx and Mathlib's `integral_cexp_quadratic`;
  * the residue at u = 0 via `dslope`, i.e. removable singularities (`vline_residue`).

  No residue theorem or general Cauchy integral formula is needed.
* Normalization λ(n) = τ(n)n^{−11/2}. Then τ(n)n^{−6−it} = λ(n)n^{−1/2−it} and
  τ(n)n^{−6+it} = λ(n)n^{−1/2+it}. The Lean statements keep τ(n)n^{−s}, `tauC n * (n:ℂ)^(-s)`.
* **Lengths.** V_{6+it}(ξ) ≈ 1 for ξ ≪ 1+|t| and decays for ξ ≫ 1+|t|. The first sum
  therefore has effective length n ≍ X(1+|t|)/2π, and the second has length (1+|t|)/(2πX). The
  product of the two lengths is ≍ (t/2π)², as required by the brief.

## 2. Headline theorems (`namespace RamanujanTau.HeckeAFE`)

```lean
-- Contour.lean (generic)
theorem vline_shift {f : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b) (hf : DifferentiableOn ℂ f (strip a b))
    (hd : GaussDecay f a b) : vline f a = vline f b
  -- GaussDecay f a b : ∃ C, ∀ x y, a ≤ x → x ≤ b → ‖f (x + y*I)‖ ≤ C * exp (-(1/2) * y^2)
theorem vline_gauss_div {b : ℝ} (hb : 0 < b) : vline (fun u => cexp (u ^ 2) / u) b = π
theorem vline_residue {F : ℂ → ℂ} {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (hF : DifferentiableOn ℂ F (strip a b)) (hM : ∃ M, ∀ u ∈ strip a b, ‖F u‖ ≤ M) :
    vline (fun u => F u * cexp (u ^ 2) / u) b - vline (fun u => F u * cexp (u ^ 2) / u) a =
      2 * π * F 0

-- Exact.lean
theorem heckeLambda_afe (s : ℂ) {X : ℝ} (hX : 0 < X) {c : ℝ} (hc : 0 < c) :
    heckeLambda s = ILam s X c + ILam (12 - s) X⁻¹ c
theorem ILam_eq_tsum {s : ℂ} {X c : ℝ} (hX : 0 < X) (hc : 0 < c) (hs : 7 < s.re + c) :
    ILam s X c = ∑' n : ℕ, tauC n * ((2 * π * n : ℝ) : ℂ) ^ (-s) * WGam s (2 * π * n / X) c
theorem tauL_afe {s : ℂ} (h5 : 5 < s.re) (h7 : s.re < 7) {X : ℝ} (hX : 0 < X) :
    tauL s = ∑' n : ℕ, tauC n * (n : ℂ) ^ (-s) * V s (2 * π * n / X) +
      eps s * ∑' n : ℕ, tauC n * (n : ℂ) ^ (s - 12) * V (12 - s) (2 * π * n * X)
theorem tauL_afe_line (t : ℝ) {X : ℝ} (hX : 0 < X) :
    tauL (6 + t * I) =
      ∑' n : ℕ, tauC n * (n : ℂ) ^ (-(6 + t * I)) * V (6 + t * I) (2 * π * n / X) +
      eps (6 + t * I) * ∑' n : ℕ, tauC n * (n : ℂ) ^ (-(6 + ((-t : ℝ) : ℂ) * I)) *
        V (6 + ((-t : ℝ) : ℂ) * I) (2 * π * n * X)
theorem norm_eps_line (t : ℝ) : ‖eps (6 + t * I)‖ = 1

-- Decay.lean   (Tq t = ‖3/2 + t I‖,  (1+|t|)/2 ≤ Tq t ≤ (3/2)(1+|t|))
theorem WGam_shift  : 0 < ξ → 0 < c₁ → c₁ ≤ c₂ → 0 < s.re + c₁ → WGam s ξ c₁ = WGam s ξ c₂
theorem WGam_residue: 0 < ξ → 0 < c → 0 < c' → c' < s.re → WGam s ξ c - WGam s ξ (-c') = Gamma s
theorem norm_Gamma_ratio_line {x : ℝ} (hx : -9 / 2 ≤ x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t y : ℝ, ‖Gamma ((6 + t * I) + ((x : ℂ) + y * I))‖ ≤
      C * Tq t ^ x * ((1 + |y|) ^ (11 / 2 + x) * Real.exp (π * |y| / 2)) * ‖Gamma (6 + t * I)‖
theorem V_decay {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ξ : ℝ, 0 < ξ → ‖V (6 + t * I) ξ‖ ≤ C * ((1 + |t|) / ξ) ^ A
theorem V_sub_one {c : ℝ} (hc0 : 0 < c) (hc : c ≤ 9 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ξ : ℝ, 0 < ξ → ‖V (6 + t * I) ξ - 1‖ ≤ C * (ξ / (1 + |t|)) ^ c
theorem V_bound {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ξ : ℝ, 0 < ξ → ‖V (6 + t * I) ξ‖ ≤ C * (1 + ξ / (1 + |t|)) ^ (-A)

-- Truncate.lean   (afeTerm t X n = τ(n) n^{−(6+it)} V(6+it, 2πn/X),  S1 t X N = Σ_{n<N} afeTerm t X n)
theorem tail_bound {A : ℝ} (hA : 3 / 4 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t X : ℝ) (N : ℕ), 0 < X → 1 ≤ N → Summable (afeTerm t X) ∧
      ‖∑' n, afeTerm t X n - ∑ n ∈ range N, afeTerm t X n‖ ≤
        C * ((1 + |t|) * X) ^ A * (N : ℝ) ^ (-(A - 3 / 4))
theorem tauL_afe_truncated_unbalanced {A : ℝ} (hA : 3 / 4 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t X : ℝ) (N₁ N₂ : ℕ), 0 < X → 1 ≤ N₁ → 1 ≤ N₂ →
      ‖tauL (6 + t * I) - (S1 t X N₁ + eps (6 + t * I) * S1 (-t) X⁻¹ N₂)‖ ≤
        C * (((1 + |t|) * X) ^ A * (N₁ : ℝ) ^ (-(A - 3 / 4)) +
          ((1 + |t|) / X) ^ A * (N₂ : ℝ) ^ (-(A - 3 / 4)))
theorem tauL_afe_truncated {η B : ℝ} (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (N : ℕ), (1 + |t|) ^ (1 + η) ≤ N →
      ‖tauL (6 + t * I) - (S1 t 1 N + eps (6 + t * I) * S1 (-t) 1 N)‖ ≤ C * (1 + |t|) ^ (-B)
theorem norm_tauL_le_afe {η B : ℝ} (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (N : ℕ), (1 + |t|) ^ (1 + η) ≤ N →
      ‖tauL (6 + t * I)‖ ≤ ‖S1 t 1 N‖ + ‖S1 (-t) 1 N‖ + C * (1 + |t|) ^ (-B)
```

Note that S1 (−t) X⁻¹ N₂ = Σ_{n<N₂} τ(n) n^{−6+it} V_{6−it}(2πnX). This is exactly the second
(dual) sum.

## 3. Proofs

1. **`vline_shift`.** Apply `Complex.integral_boundary_rect_eq_zero_of_differentiableOn` to the
   rectangle [a,b] × [−R,R]. The horizontal sides are ≤ C e^{−R²/2}(b−a) → 0. The vertical sides
   converge by `intervalIntegral_tendsto_integral`. Uniqueness of limits gives I·(V_b − V_a) = 0.
2. **`vline_gauss_div`.**
   * Write 1/u = ∫_0^∞ e^{−ux}dx (`integral_exp_mul_complex_Ioi`).
   * Swap the integrals by Fubini. The integrand is dominated by e^{b²}e^{−y²}·e^{−bx}.
   * The inner integral is ∫_y e^{u²−ux} dy = √π e^{−x²/4} (`integral_cexp_quadratic`).
   * Then ∫_0^∞ √π e^{−x²/4} dx = π.

   The case a < 0 gives −π by y ↦ −y, since e^{u²}/u is odd.
3. **`vline_residue`.**
   * Split F(u)e^{u²}/u = dslope F 0 (u)·e^{u²} + F(0)e^{u²}/u.
   * The first term is holomorphic (`Complex.differentiableOn_dslope`). It is bounded: by
     compactness on the unit disc, and by 2M/|u| outside it. It shifts freely by step 1.
   * The second term contributes F(0)(π − (−π)).
4. **`heckeLambda_afe`.**
   * Take F(u) = Λ(s+u)X^u. It is bounded on strips by `heckeLambda_bdd_strip`.
   * Residue at u = 0: V_c − V_{−c} = 2πΛ(s).
   * Reflect the line −c by u ↦ −u (`vline_neg_eq`). Hecke's equation gives
     Λ(s−u) = Λ(12−s+u), and X^{−u} = (1/X)^u. So V_{−c} = −2π I_Λ(12−s; 1/X).
5. **`ILam_eq_tsum`.**
   * For Re(s+u) > 7, Λ(s+u) = (2π)^{−s−u}Γ(s+u)Σ τ(n)n^{−s−u}.
   * The powers satisfy (2π)^{−(s+u)}n^{−(s+u)}X^u = (2πn)^{−s}(2πn/X)^{−u} (`power_key`, via
     exp∘log).
   * Swap sum and integral by `integral_tsum_of_summable_integral_norm`. The domination uses
     \|Γ(w)\| ≤ Γ(Re w) (`RankinError.norm_Gamma_le_Gamma_re`), and summability uses
     Σ\|τ(n)\|n^{−σ} < ∞ for σ > 13/2 (`HeckeConvex.summable_abs_tau_div_rpow`).
6. **`tauL_afe`.** Use `tauL s = (2π)^s Γ(s)^{−1} Λ(s)` and split. **`norm_eps_line`**: on the
   line, 12 − s = s̄, so \|Γ(12−s)\| = \|Γ(s)\| by `Gamma_conj`, and \|(2π)^{2it}\| = 1.
7. **Weights.**
   * `WGam_shift` and `WGam_residue` are the generic lemmas applied with F(u) = Γ(s+u)ξ^{−u},
     with \|Γ\| bounded on compact strips of Re > 0.
   * `norm_Gamma_ratio_line` combines the Stirling upper bound at σ = 6+x, with
     T(t+y)^{11/2+x} ≤ T(t)^{11/2+x}(1+\|y\|)^{11/2+x}, and the Stirling lower bound at σ = 6.
     Both are from `Stirling.Absolute`. Also e^{−π\|t+y\|/2} ≤ e^{−π\|t\|/2}e^{π\|y\|/2}.
     Only T(t+y) ≤ T(t)(1+\|y\|) is needed, because the exponent 11/2 + x is ≥ 1 > 0.
   * Then (1+\|y\|)^q e^{π\|y\|/2}e^{−y²} ≤ e^{(q+π/2)²/2}e^{−y²/2} (`poly_exp_bound`).
     Integrating gives `W_line_bound`: \|W_{6+it}(ξ)\|_{Re u = x} ≤ K (T(t)/ξ)^x \|Γ(6+it)\|.
   * `V_decay` shifts from c = 2 to c = A. `V_sub_one` crosses to c = −c′ and uses the residue
     Γ(s). `V_bound` combines the two, with V_decay at A + 1 and V_sub_one at c = 1.
8. **Truncation.**
   * \|τ(n)n^{−6}V(2πn/X)\| ≤ C((1+\|t\|)X)^A·\|τ(n)\|/n^{6+A}.
   * For n ≥ N, \|τ(n)\|/n^{6+A} ≤ N^{−(A−3/4)}\|τ(n)\|/n^{27/4}, and Σ\|τ(n)\|n^{−27/4} < ∞.
     This is the reason for the 3/4.
   * Taking A = (B + ¾(1+η))/η + ¾ and N ≥ (1+\|t\|)^{1+η} gives the error (1+\|t\|)^{−B}.

## 4. Numerical checks (evidence level 4)

PARI scripts: `scripts/hecke_afe/afe_check.gp` and `ms_check.gp`, with outputs in `*.out`.
Settings: `nbthreads = 1`, 28 digits.

The weight V is computed by the trapezoid rule in y, with step 1/40 on [−12, 12]. This is
spectrally accurate, because the integrand is analytic in \|Im y\| < c and Gaussian. PARI's
`intnum` on [−12, 12] is **not** reliable here: it returns 0.5405 for (1/2π)∫e^{u²}/u dy, whose
true value is 1/2. The trapezoid rule gives 0.5000000000000000000.

1. **Contour independence and residue.**
   * \|V(c=2) − V(c=5)\| ≤ 4·10⁻²⁶.
   * \|V(c=2) − 1 − V(c=−1)\| ≤ 6·10⁻³⁵.
   * Checked at (t, ξ) = (10, 3), (50, 20), (50, 400), (1000, 5000).
2. **The AFE.**
   * \|L(6+it) − AFE_N\| ≈ 3–9·10⁻¹¹ at t ∈ {0.5, 1, 10, 30, 60}, for X ∈ {1, 2, 1/2, 4}.
   * The truncation is N = (\|t\|+6)e⁸max(X,1/X)/2π, up to 68 319 terms. The residual is the
     truncation error, as expected.
   * \|ε\| − 1 < 10⁻⁴⁰.
   * The weight e^{u²} makes V decay like e^{−(log(ξ/t))²/4} in log-scale. That is correct, but
     it needs long sums at high precision.
3. **Uniformity (V_bound).**
   * max_r \|V\|(1+r)^A for t = 10, 10², 10³, 10⁴ is 10.9 / 12.7 / 13.5 / 13.6 at A = 2, and
     1.16 / 1.02 / 1.11 / 1.12 ·10⁶ at A = 4. So it is bounded in t. The large A = 4 constant
     reflects e^{c²} at c = A.
   * max \|V−1\|/r over r ≤ 1/16 is 0.54 / 0.68 / 0.69 / 0.69. This is V_sub_one with c = 1.
4. **Mean square against `CriticalMeanSquareAsymp`.**
   * With X = 1, the AFE diagonal is D(t) = 2Σλ(n)²/n·\|V_t(2πn)\|², using \|V_{−t}\| = \|V_t\|.
   * The table below gives (1/T)∫_T^{2T} \|L\|² and (1/T)∫_T^{2T} D.

     | T | ⟨\|L\|²⟩ | ⟨D⟩ | increment of ⟨\|L\|²⟩ | increment of ⟨D⟩ |
     |---|---|---|---|---|
     | 25 | 2.680 | 3.130 | | |
     | 50 | 3.499 | 3.803 | 0.819 | 0.673 |
     | 100 | 4.045 | 4.348 | 0.546 | 0.545 |
     | 200 | 4.441 | 4.877 | 0.396 | 0.529 |

   * Under T → 2T, both should increase by 2c·log 2 = **0.5325** (2c = `cDelta` = 0.768168).
   * The diagonal does this cleanly (0.545, 0.529). The raw \|L\|² averages fluctuate around it,
     with Good's error O((T log T)^{2/3}).
   * The O(1) offset between ⟨\|L\|²⟩ and ⟨D⟩ is expected. The cross terms ε(t)Σ_{mn ≈ (t/2π)²}
     contribute O(1) on average, so the constant in Good's secondary term is *not* the diagonal
     constant.
   * In summary, the AFE's diagonal reproduces the leading constant 2c of
     `critical_mean_square_asymptotic`. Paper-level reason: Σ_{n≤x}λ(n)²/n ~ c log x (Rankin,
     `rankin_normalization`), and the two sums have lengths whose product is (t/2π)², so
     D(t) ~ c log((t/2π)²) = 2c log(t/2π).

## 5. Goal 2: the twisted second moment (not done; plan and exact hypothesis)

Target, for coprime h, k ≤ T^θ and a smooth w supported in [1, 2]:

    ∫ |L(6+it)|² (h/k)^{it} w(t/T) dt = (T/√(hk)) · P_{h,k}(log T) + O(T^{1−δ}(hk)^{A}),

where P_{h,k} is linear and comes from Σ_r λ(hr)λ(kr)r^{−1−2v} at v = 0. The double pole of
L(Δ×Δ, 1+2v)·(local factors at p | hk) gives the log T.

**Route via `tauL_afe_truncated_unbalanced` (X = 1).**

1. Expand \|S₁ + εS₂\|². The terms S₁S̄₁ and S₂S̄₂ give Σ_{m,n} λ(m)λ(n)(mn)^{−1/2}
   ∫ V_t V̄_t w (hn/km)^{it} dt.
   * The weights V depend on t. Separate variables by writing V_t through its Mellin integral
     (Re u = 2). The t-dependence is then the Γ-ratio Γ(6+it+u)/Γ(6+it). It is a smooth amplitude
     of size (1+\|t\|)^{Re u}, with derivatives in t of relative size O(1/t). That is the
     content of `norm_Gamma_ratio_line`, plus one more derivative bound, which is not yet
     formalized.
   * Integration by parts in t kills every (m, n) with \|hn − km\| ≥ T^{ε}·km/T.
2. **Diagonal hn = km**, i.e. n = kr, m = hr. This gives the main term, through the
   Rankin–Selberg series twisted at p | hk. Inputs: `RankinSelberg` / `RankinError` and the
   local Hecke relations (`HeckeTheory`).
3. **Off-diagonal hn − km = ℓ ≠ 0** with \|ℓ\| ≤ T^{ε}hk·(length/T). This requires a two-sided
   shifted-convolution bound:

```lean
noncomputable def shiftSum2 (a b : ℕ) (ℓ : ℤ) (N : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, if (a : ℤ) * m - b * n = ℓ then lam m * lam n else 0
def SCS2 (η B : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b : ℕ) (ℓ : ℤ) (N : ℕ), 1 ≤ a → 1 ≤ b → ℓ ≠ 0 →
    |shiftSum2 a b ℓ N| ≤ C * ((N : ℝ) + |(ℓ : ℝ)|) ^ (1 - η) * ((a * b : ℕ) : ℝ) ^ B
```

   This is in `Hyp.lean`, with `SCS2.mono`. The case a = b = 1 is the repo's one-sided
   `SubconvexityCond.ShiftedConvolutionBound`. Sharp cutoffs suffice, by two-variable partial
   summation against the smooth weights. Any η > 0 with polynomial (ab)^B is enough for θ small
   (θ < η/(2B+O(1))).
   Literature: Jutila; Blomer (2004), "Shifted convolution sums and subconvexity bounds for
   automorphic L-functions"; Blomer–Harcos (2008), "The spectral decomposition of shifted
   convolution sums".
4. **Cross terms S₁ε̄S̄₂.** These are Σλ(m)λ(n)(mn)^{−1/2}∫ε̄(t)(mn)^{−it}(h/k)^{it}…. The phase of
   ε(t) is −2t log(t/2πe) + O(1/t), so stationary phase at t₀ = 2π√(mnk/h)… lies outside
   [T, 2T] unless mn ≍ (T/2π)²·(k/h). Their total is O(T^{1/2+ε}(hk)^{O(1)}): the first-derivative
   test plus the Γ-ratio phase expansion. That needs `DigammaAsymp`-level Stirling for arg Γ,
   which is available in `ZeroCountRvM`.

**Estimate.** About 3–5k lines, as in `HAFNER_PROPORTION.md`:

* separated-variables Mellin bookkeeping and the t-derivative bound on Γ-ratios: ~600;
* integration by parts and truncation to \|hn − km\| small: ~600;
* diagonal main term with the twisted Rankin–Selberg series: ~1–1.5k;
* off-diagonal from `SCS2`: ~400;
* cross terms by stationary phase: ~800–1200.

`SCS2` itself (Kloosterman / spectral) is a separate project of 3k+ lines. It generalizes
`SCSProof`'s Poincaré-series route to Γ₀(ab)-type level.

## 6. Gaps

* **Goal 2 is not formalized.** §5 gives the plan and the exact hypothesis. `SCS2` is a typed
  statement only; nothing uses it yet.
* **No t-derivative bounds for V_t.** These are the bounds ∂_t^j V_t(ξ) ≪ (1+\|t\|)^{−j}(…),
  needed for integration by parts in Goal 2 and in (SK). They follow from the same Mellin
  representation and from ψ-bounds for Γ′/Γ, but they are not done.
* **No AFE-derived mean value in Lean.** The mean-square consequence is checked only
  numerically. The Lean asymptotic `critical_mean_square_asymptotic` (2c T log T) comes from a
  different route (Hecke–Hafner rays plus Karamata), so the leading constant is cross-checked
  rather than re-derived.
* **Scope.** Only the line Re s = 6 is uniform in Lean. `tauL_afe` holds in 5 < Re s < 7 as an
  identity, but the weight bounds are stated at σ = 6. Moving σ only changes constants in
  `norm_Gamma_ratio_line`.
* **The weight G(u) = e^{u²} gives large constants.** C_A ≈ e^{A²}, and V decays like
  e^{−(log ξ/t)²/4}. This is harmless for ≪-statements. For explicit numerics, a G with
  G(u) = 0 at the poles, or a compactly supported Mellin weight, would converge faster.

## Files

| file | lines | content |
|---|---|---|
| `Contour.lean` | 315 | `vline`, `strip`, `GaussDecay`, `vline_shift`, `inner_gauss`, `vline_gauss_div(_neg)`, `vline_neg_eq`, `dslope_bdd`, `vline_residue` |
| `Exact.lean` | 333 | `ILam`, `WGam`, `heckeLambda_afe`, `power_key`, `ILam_eq_tsum`, `V`, `eps`, `tauL_afe`, `tauL_afe_line`, `norm_eps_line` |
| `Decay.lean` | 388 | `gamma_bdd_strip`, `WGam_shift`, `WGam_residue`, `Tq`, `norm_Gamma_ratio_line`, `poly_exp_bound`, `W_line_bound`, `V_decay`, `V_sub_one`, `V_bound` |
| `Truncate.lean` | 216 | `afeTerm`, `tail_bound`, `S1`, `afe_line_eq`, `tauL_afe_truncated_unbalanced`, `tauL_afe_truncated`, `norm_tauL_le_afe` |
| `Hyp.lean` | 46 | `shiftSum2`, `SCS2`, `SCS2.mono` (statement for Goal 2) |
| `Main.lean` | 44 | imports and `#print axioms` |

Reused: `HeckeL` (`heckeLambda`, FE, `heckeLambda_bdd_strip`, `heckeLambda_eq`, `tauL`),
`Stirling.Absolute` (`norm_Gamma_le_stirling`, `stirling_le_norm_Gamma`),
`RankinError.GammaBound.norm_Gamma_le_Gamma_re`, `HeckeConvex.summable_abs_tau_div_rpow`,
`SubconvexityCond.Defs.lam`. Mathlib: `integral_boundary_rect_eq_zero_of_differentiableOn`,
`integral_cexp_quadratic`, `integral_gaussian_complex_Ioi`, `Complex.differentiableOn_dslope`,
`integral_tsum_of_summable_integral_norm`.

## Literature

- H. Iwaniec, E. Kowalski, *Analytic Number Theory*, Thm 5.3 (smoothed AFE, G(u) = e^{u²}-type
  weights) and Prop 5.4.
- E. Hecke, Math. Ann. 112 (1936); A. Good, Mathematika 29 (1982); J. L. Hafner, Math. Ann. 264
  (1983).
- V. Blomer, *Shifted convolution sums and subconvexity bounds for automorphic L-functions*,
  IMRN 2004; V. Blomer, G. Harcos, *The spectral decomposition of shifted convolution sums*,
  Duke Math. J. 144 (2008).

---

## 2026-11-06 (II): t-derivative of the weight (`RamanujanTau/HeckeAFE2/`)

Build: `nice -n 10 lake build RamanujanTau.HeckeAFE2.Main` exits 0. The module has 3 files and
618 lines. All 6 headlines print `[propext, Classical.choice, Quot.sound]`. There is no
`sorry`, `axiom` or `native_decide`.

**Status.**
* Item (a) of the follow-up brief is done for **j = 1**.
* Item (b), the twisted second moment conditional on `SCS2`, is **not** done.
* The fallback, the untwisted mean value derived from the AFE in Lean, is **not** done.
* The reasons are given below.

### Headlines (`namespace RamanujanTau.HeckeAFE2`, level 1)

```lean
-- Psi.lean
theorem norm_digamma_sub_log_le {z : ℂ} (hz : 2 ≤ z.re) :
    ‖digamma z - log z‖ ≤ 40 / (z.re - 1 + |z.im|)
theorem norm_digamma_diff_le {x : ℝ} (hx : -1 ≤ x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t y : ℝ,
      ‖digamma ((6 + t * I) + ((x : ℂ) + y * I)) - digamma (6 + t * I)‖ ≤
        C * (1 + |y|) ^ 2 / (1 + |t|)
-- Deriv.lean   (Fi x ξ t y = Γ(6+it+u) ξ^{−u} e^{u²}/u,  u = x+iy)
theorem hasDerivAt_Phi (hx : -1 ≤ x) (hx0 : x ≠ 0) (hξ : 0 < ξ) (t₀ : ℝ) :
    HasDerivAt (fun t => ∫ y : ℝ, Fi x ξ t y) (∫ y : ℝ, Fi' x ξ t₀ y) t₀
theorem hasDerivAt_Vline (hx : -1 ≤ x) (hx0 : x ≠ 0) (hξ : 0 < ξ) (t : ℝ) :
    HasDerivAt (Vline x ξ) (Dline x ξ t) t
  -- Vline x ξ t = (2π)⁻¹ ∫ Fi / Γ(6+it) = WGam (6+it) ξ x / Γ(6+it)
  -- Dline x ξ t = (2π)⁻¹ ∫ i(ψ(6+it+u) − ψ(6+it)) Fi x ξ t y dy / Γ(6+it)
theorem norm_Dline_le (hx : -1 ≤ x) (hx0 : x ≠ 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ξ : ℝ, 0 < ξ → ‖Dline x ξ t‖ ≤ K * (Tq t / ξ) ^ x / (1 + |t|)
theorem V_deriv_bound {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ξ : ℝ, 0 < ξ →
      HasDerivAt (fun w : ℝ => V (6 + w * I) ξ) (deriv (fun w : ℝ => V (6 + w * I) ξ) t) t ∧
      ‖deriv (fun w : ℝ => V (6 + w * I) ξ) t‖ ≤ C / (1 + |t|) * (1 + ξ / (1 + |t|)) ^ (-A)
```

### Proof

1. **The saving 1/t comes from the ψ-difference.** Write
   ψ(z) − ψ(s) = (log z − log s) + (ψ(z) − log z) − (ψ(s) − log s).
   * The first bracket is handled by the mean-value inequality on the segment [s, z], which lies
     in Re > 0, with |1/w| ≤ 2(1+|y|)/(1+|t|) there.
   * The other two brackets are O(1/|z|), by `norm_digamma_sub_log_le`. Its proof generalizes the
     repo's `ZeroCountRvM.norm_digamma_six_sub_log_le`, via ψ = log + Σ e_j and
     |e_j(z)| ≤ 20|z+j|^{−2}.
2. **Differentiating under the integral.**
   * Use `hasDerivAt_integral_of_dominated_loc_of_deriv_le` on the ball |t − t₀| < 1.
   * The domination is crude but enough: |Γ′(z)| = |ψ(z)||Γ(z)| ≤ (|z| + π + 10)·Γ(6+x), times
     a Gaussian.
   * The quotient rule then gives Φ′ − iψ(s)Φ = ∫ i(ψ(s+u) − ψ(s))Γ(s+u)K. The pole at u = 0
     has been cancelled by the difference ψ(s+u) − ψ(s).
3. **Bounding the derivative.**
   * `norm_Dline_le` is the analogue of `W_line_bound`, with one extra factor
     C(1+|y|)²/(1+|t|).
   * Since V(6+it, ξ) equals `Vline x ξ t` for every x > 0 (`WGam_shift`) and equals
     1 + `Vline (-1) ξ t` (`WGam_residue`), its derivative can be computed on any line.
     Line x = A+1 handles large ξ, and line x = −1 handles small ξ. `combine_bound` merges the
     two regimes.

Numerical check (level 4): `scripts/hecke_afe/deriv_check.gp` uses centred differences.

| t | max_r (1+t)\|∂_tV\| | max_r (1+t)\|∂_tV\|(1+r)² |
|---|---|---|
| 10 | 0.363 | 21.3 |
| 10² | 0.507 | 27.5 |
| 10³ | 0.521 | 29.1 |
| 10⁴ | 0.523 | 29.2 |

Both quantities are bounded in t, as the theorem predicts.

### What is still missing, and the honest size of (b)

* **j ≥ 2.** Integration by parts in ∫ V_t(m)V̄_t(n) w(t/T)(hn/km)^{it} dt needs about A/ε
  derivatives, to dispose of every pair with |log(hn/km)| ≥ T^{−1+ε}. Proposed route:
  * Cauchy estimates for g = ψ − log on discs of radius |z|/2 give g^{(k)} = O(|z|^{−1−k}).
  * Hence the k-th t-derivative of L(t) = log Γ(s+u) − log Γ(s) is O((1+|y|)^{k+1}/(1+|t|)^k).
  * Faà di Bruno then gives ∂_t^j(Γ(s+u)/Γ(s)) = R·P_j(L′, …, L^{(j)}).
  * About 400–600 lines. The j = 1 file above is the template.
* **(b) the twisted second moment, conditional on `SCS2`.** Not attempted in Lean.
  * Still needed: separation of variables and t-integration by parts (needs j ≥ 2); the diagonal
    hn = km with its exact main term; the off-diagonal via `SCS2`; and the ε-cross terms by
    stationary phase.
  * Estimate unchanged: 3–5k lines.
* **The main term, paper level, not checked in Lean or numerically.** For coprime h, k define
  D_{h,k}(s) = Σ_r λ(hr)λ(kr) r^{−s} (Re s > 1).
  * D_{h,k} has a simple pole at s = 1, coming from L(Δ×Δ, s) = ζ(s)L(Sym²Δ, s)/ζ(2s) and
    local factors at p | hk.
  * Write D_{h,k}(1+v) = R₋₁/v + R₀ + O(v).
  * Then ∫|L(6+it)|²(h/k)^{it}w(t/T)dt = (1/√(hk)) ∫ w(t/T)[R₋₁·(log(t²/(4π²)) + κ) + 2R₀] dt
    + O(T^{1−δ}(hk)^C).
  * Here κ is a Γ-constant that comes from the shifted moment at α = β = 0. It is not
    determined here.
  * For h = k = 1, R₋₁ = c (Rankin's constant, `rankinC`), so the leading term is
    2c·T log T·∫w/T. This is consistent with `cDelta = 2c` in `CriticalMeanSquareAsymp`.
* **The untwisted case h = k = 1 via the AFE (the fallback).** This is also not short.
  * One cannot freeze the t-dependent weights on t-blocks. The j = 1 bound makes the
    block-freezing error O(H·T^{−1/2}), which forces H ≲ T^{1/2}. The Montgomery–Vaughan error
    O(Σ n|a_n|²) = O(T) per block then exceeds the block's main term H log T.
  * So even h = k = 1 needs the off-diagonal and ε-cross-term analysis, i.e. j ≥ 2 integration by
    parts and stationary phase. It is about 2–3k lines.
  * The Lean mean-square asymptotic with constant 2c already exists by the ray/Karamata route
    (`CriticalMeanSquareAsymp`). The AFE-diagonal cross-check is numerical (§4.4 above).

Files: `HeckeAFE2/Psi.lean` (169 lines), `HeckeAFE2/Deriv.lean` (432), `HeckeAFE2/Main.lean`
(17), `scripts/hecke_afe/deriv_check.gp` and `.out`.
