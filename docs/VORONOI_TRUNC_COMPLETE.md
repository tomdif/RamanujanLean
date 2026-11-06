# Voronoi, Cramér and `Ω±` for every nonzero level-one cusp form: no `a(1) ≠ 0`, complex coefficients

Lean: `RamanujanTau/VoronoiTruncComplete/` (3 files, about 870 lines). There is no `sorry`, no
`native_decide`, no new axiom and no named hypothesis. Build with
`nice -n 10 lake build RamanujanTau.VoronoiTruncComplete.Main` (exit 0). `#print axioms` gives
`[propext, Classical.choice, Quot.sound]` for every headline. **Evidence level (1).** Deligne is not
used. `RamanujanTau.lean` does not import this directory.

This closes the two gaps in §5 of `docs/VORONOI_TRUNC_GENERAL.md`:

1. `Ω±` without assuming `a(1) ≠ 0`;
2. complex coefficients.

## 1. Statements

Notation: `a(n) = coef f n ∈ ℂ` and `S_f(x) = Σ_{1≤n≤x} a(n)`. The only hypothesis on `f` is
`f ∈ S_k(SL₂(ℤ))`, `f ≠ 0`. That hypothesis forces `k = 2m` with `m ≥ 6`.

```lean
-- namespace RamanujanTau.VoronoiTruncComplete   (Main.lean)
theorem cusp_omega_pm_exact' (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0)
    (hreal : ∀ n, (coef f n).im = 0) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ coef f n₀ ≠ 0 ∧ (∀ n < n₀, coef f n = 0) ∧
      ∀ c : ℝ, c < |(coef f n₀).re| * (n₀ : ℝ) ^ (-((k : ℝ) / 2 + 1 / 4)) / (2 * π * √2) →
        ∀ᶠ X in atTop,
          (∃ x ∈ Icc X (2 * X), c * x ^ (((k : ℝ) - 1) / 2 + 1 / 4) < ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (coef f n).re) ∧
          (∃ x ∈ Icc X (2 * X), ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (coef f n).re < -c * x ^ (((k : ℝ) - 1) / 2 + 1 / 4))

theorem cusp_re_omega_pm (f) (hf : f ≠ 0) {n₀} (h0 : 1 ≤ n₀) (hz : ∀ n < n₀, (coef f n).re = 0)
    (hn₀ : (coef f n₀).re ≠ 0) {c} (hc : c < |(coef f n₀).re| * n₀ ^ (-(k/2 + 1/4)) / (2π√2)) :
    ∀ᶠ X in atTop, (∃ x ∈ Icc X (2X), c x^{(k−1)/2+1/4} < (∑ n ∈ Icc 1 ⌊x⌋₊, coef f n).re) ∧
                   (∃ x ∈ Icc X (2X), (∑ …).re < −c x^{(k−1)/2+1/4})
theorem cusp_im_omega_pm …   -- the same with .im in place of .re

theorem cusp_cramer_complex (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) :
    Tendsto (fun X : ℝ => (∫ x in (1 : ℝ)..X, ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coef f n‖ ^ 2) /
        X ^ ((k : ℝ) + 1 / 2)) atTop
      (𝓝 ((∑' n : ℕ, ‖coef f n‖ ^ 2 * (n : ℝ) ^ (-((k : ℝ) + 1 / 2))) / ((4 * k + 2) * π ^ 2)))

theorem cusp_voronoi_truncated_L2_complex (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 4) :
    Tendsto (fun X : ℝ => (∫ x in X..2 * X,
        ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, coef f n -
          ((x ^ (((k : ℝ) - 1) / 2 + 1 / 4) / (π * √2) : ℝ) : ℂ) * ∑ n ∈ Finset.Icc 1 ⌊X ^ θ⌋₊,
            coef f n * (((n : ℝ) ^ (-((k : ℝ) / 2 + 1 / 4)) *
              Real.cos (4 * π * √((n : ℝ) * x) - π / 4) : ℝ) : ℂ)‖ ^ 2) /
        X ^ ((k : ℝ) + 1 / 2)) atTop (𝓝 0)

-- supporting results
theorem exists_first_coef (f) (hf : f ≠ 0) : ∃ n₀, 1 ≤ n₀ ∧ coef f n₀ ≠ 0 ∧ ∀ n < n₀, coef f n = 0
theorem eq_zero_of_coef (f) (h : ∀ n, coef f n = 0) : f = 0
theorem vdata_re_mul (hk : k = 2m) (hm : 2 ≤ m) (f) (w : ℂ) : VData m (fun n => (w * coef f n).re)
theorem omega_pm_first (hd : VData m a) (h0 : 1 ≤ n₀) (hz : ∀ n < n₀, a n = 0) (hn₀ : a n₀ ≠ 0)
    (hc : c < |a n₀| n₀^{−(m+1/4)}/(2π√2)) : …Ω± for Sre a…
```

In words:

- **(B″)** Let `f ≠ 0` be real and let `a(n₀)` be its first nonzero coefficient. Then `S` is
  `Ω±(x^{(k−1)/2+1/4})` in every dyadic interval, for any constant
  `c < |a(n₀)| n₀^{−(k/2+1/4)}/(2π√2)`. For `n₀ = 1` this is `cusp_omega_pm_exact`.
- **(B″ for complex `f`)** The same holds for `Re S_f`, at the first `n` with `Re a(n) ≠ 0`, and for
  `Im S_f`, at the first `n` with `Im a(n) ≠ 0`. At least one of these two applies to every `f ≠ 0`.
- **(B, complex)** `∫₁^X |S_f|² ~ X^{k+1/2} Σ|a(n)|² n^{−(k+1/2)}/((4k+2)π²)`.
- **(A, complex)** The complex truncated Voronoi sum `V_f` approximates `S_f` in mean square on
  dyadic blocks, for `0 < θ ≤ 1/4`.

## 2. Proofs

### Gap 1: the kernel at the first nonzero frequency (`Omega0.lean`)

Ingham's kernel is `ρ(x) = 1 ± cos θ_{n₀}(x)`, with `θₙ(x) = 4π√(nx) − π/4`. The new estimate is
`term_int0`. For `n ≥ n₀` it says

    ∫_X^{2X} cos θₙ · ρ = ±[n = n₀] X/2 + O((2 + √(n₀+1) + √n₀) √(2X)/π).

The product splits into three oscillating cosines with frequencies `√n`, `√n − √n₀` and `√n + √n₀`.
Each is integrated by parts once (`abs_integral_cos_le`).

The task asked what the frequencies `n > n₀` contribute. Since `a(n) = 0` for `n < n₀`, they are the
only off-diagonal terms. For them,

    √n − √n₀ ≥ √(n₀+1) − √n₀ = 1/(√(n₀+1) + √n₀)   (`inv_gap_le`).

This lower bound is a constant: it depends on neither `X` nor `N`. So each off-diagonal term is still
`O(√X)`, with constant `√(n₀+1) + √n₀`. This is not the `X^{1/8}` loss predicted in
`VORONOI_TRUNC_GENERAL.md` §5, which would only arise for frequencies below `n₀`, and there are none.

The remaining steps of `omega_core0` are copied from `omega_core`, with `3` replaced by
`2 + √(n₀+1) + √n₀`:

- the main term is `Σ|bₙ| · O(√X) ≤ X^{1/8} St · O(√X) = O(X^{5/8})`;
- the remainder `S − V_N` is handled by `voronoi_L2` with an AM–GM split;
- the window must satisfy `N = ⌊X^{1/4}⌋ ≥ n₀`, which holds eventually.

`omega_pm_first` rescales `a` by `1/(a(n₀) n₀^{−(m+1/4)})` (`VData.smul`). The signs swap when that
factor is negative.

### Gap 2: complex coefficients (`Complex.lean`)

This needs neither a real basis of `S_k` nor a Hermitian `mean_value`. For any `w ∈ ℂ`, the real
sequence `b(n) = Re(w a(n))` satisfies `VData m b` directly (`vdata_re_mul`):

- **Modular relation.** Put `G(z) = Σ a(n) e^{−2πnz} = f(iz)`. Then
  `G(z) = (−1)^m z^{−2m} G(1/z)` (`G_modular`). From `Re c = (c + c̄)/2` and
  `conj e^{−2πn z̄} = e^{−2πnz}` we get `D_b(z) = (wG(z) + conj(wG(z̄)))/2` (`Dq_re_eq`). Since
  `conj((z̄)⁻¹) = z⁻¹` and `conj((z̄)^{2m})⁻¹ = (z^{2m})⁻¹`, the relation for `G` at `z` and at `z̄`
  gives the relation for `D_b`.
- **Rankin.** `b(n)² ≤ ‖w‖² ‖a(n)‖²`, together with `HeckeConvexGeneral.sum_sq_le`.

The choice `w = 1` gives `Re a` and `w = −i` gives `Im a`. Then `|S_f|² = (S_{Re a})² + (S_{Im a})²`.
Also `Re V_f = V_{Re a}` and `Im V_f = V_{Im a}`, because the kernel is real. So the complex
statements are the sums of the two real ones: `cramer_core` and `voronoi_L2` applied to `Re a` and
`Im a`. The two Cramér constants add up to `Σ‖a(n)‖² n^{−(k+1/2)}`.

As a by-product, the abstract real results (`VoronoiTruncGeneral`) now apply to `Re a` and `Im a`
of *every* cusp form. The hypothesis `hreal` is only needed to phrase statements about `S_f` itself.

`eq_zero_of_coef`: if every `a(n)` vanishes then `f = 0`. The proof evaluates
`f(τ) = Σ a(n) e^{2πinτ}` at `τ = i(−iτ)` (`hasSum_coef_exp`).

## 3. Files

| file | content |
|---|---|
| `Omega0.lean` | `rho0`, `inv_gap_le`, `term_int0`, `main_int0`, `omega_core0`, `omega_plus0/minus0`, `omega_pm_first`, `exists_first` |
| `Complex.lean` | `G`, `G_modular`, `Dq_re_eq`, `vdata_re_mul`, `vdata_re`, `vdata_im`, `eq_zero_of_coef` |
| `Main.lean` | headlines, `Vf`, `Vf_re`, `Vf_im`, `#print axioms` |

The following are reused unchanged from `VoronoiTruncGeneral`: `VData`, `voronoi_L2`,
`cramer_core`, `abs_integral_cos_le`, `sum_abs_bco_le`, `tendsto_d`, the integrability lemmas,
`exists_half`, `exps`, `Vth_eq_explicit`, `hasSum_coef_exp`, `cusp_S` and `coef_eq_re`.

## 4. Numerical checks (evidence level (4); `scripts/voronoi_trunc_complete/`)

`check_complete.gp` (output in `check_complete.out`) works in `S_24`, which has dimension 2. It uses
`g = ΔE₄³` (with `a(1) = 1`) and `h = Δ²` (with `a(1) = 0`, `a(2) = 1`, so `n₀ = 2`).

- **Kernel at `n₀ = 2`.** This checks the constant directly. The prediction for
  `X⁻¹∫_X^{2X} S_h x^{−e}(1 ± cos θ₂)` is `±a(2)·2^{−(m+1/4)}/(2π√2) = ±2.3104e−5`.

  | X | `s = +1` | `s = −1` | ratio (+) |
  |---|---|---|---|
  | 2000 | 2.1767e−5 | −2.2273e−5 | 0.942 |
  | 8000 | 2.2793e−5 | −2.2926e−5 | 0.987 |
  | 16000 | 2.3006e−5 | −2.2972e−5 | 0.996 |

  The frequency-1 kernel applied to `h` gives `−2.9e−7`, which is about 0 as it should be. On
  `[8000, 16000]`, `max S_h/x^e = 1.36e−4` and `min = −1.46e−4`. Both are far beyond the threshold
  `2.31e−5`; the constant is not sharp.
- **Complex Cramér** for `f = ΔE₄³ + iΔ²`. The prediction is `B_f/(98π²) = 1.8970e−3`. The observed
  ratios are `0.987`, `0.971` and `1.011` at `X = 4000`, `16000` and `32000`. The swings are the usual
  oscillation of the lower-order term.
- **Complex `L²` Voronoi.** Mean of `|S−V_N|²/x^{k−1/2}`:
  - `1.10e−2` at `X = 2000`, `N = 20`;
  - `3.75e−3` at `X = 8000`, `N = 120`.

  For comparison, the mean of `|S|²/x^{k−1/2}` is `4.65e−2`, against `B_f/(4π²) = 4.648e−2`.

## 5. Gaps

- **Rate for complex `f`.** The explicit-rate version `cusp_voronoi_truncated_L2_rate` was not
  restated for complex `f`. It follows by adding the two real majorants (with constant
  `C_{Re} + C_{Im}` and tail `Σ_{n>N}‖a(n)‖² n^{−(k+1/2)}`), but this was not written out.
- **`Ω±` for complex `f`** is stated for `Re S_f` and `Im S_f` separately. Nothing is proved for
  `Re(e^{−iφ} S_f)` in other directions φ, although that would follow in the same way from
  `vdata_re_mul` with `w = e^{−iφ}`. Nothing is proved about `|S_f|` either, beyond the mean square.
- **The constant** `|a(n₀)| n₀^{−(k/2+1/4)}/(2π√2)` is not sharp. Numerically, the extremes exceed it
  by a factor of about 6. Other gaps are as in `docs/VORONOI_TRUNC_GENERAL.md` §5: `θ ≤ 1/4` only,
  `L²` rather than pointwise, and no higher moments.

## 6. Literature (from memory, not checked against sources)

- Ingham (1942): the positive-kernel method for `Ω±`. Using the first nonzero frequency is standard.
- Chandrasekharan–Narasimhan (1962): Voronoi and `Ω±` for general Dirichlet series with functional
  equation.
- Cramér (1922) and Tong (1956): mean squares.

No novelty claim is made.
