# A zero-free region of de la Vallée-Poussin type for `L(Δ,s)`

Lean: `RamanujanTau/ZeroFreeRegion/` (7 files, about 1440 lines, no `sorry`, no new axiom, no
`native_decide`). Build with `nice -n 10 lake build RamanujanTau.ZeroFreeRegion.Main`; it exits 0.
The public entry point is included in the `RamanujanTau.lean` import graph.

**Evidence level (1).** The results are unconditional and axiom-clean. Every headline prints
`[propext, Classical.choice, Quot.sound]`. There are no named hypotheses, and Deligne's bound
`|τ(p)| ≤ 2p^{11/2}` is not used.

## Statements

```lean
-- Region.lean
theorem tauL_zero_free_region : ∃ c > 0, ∃ t₀ : ℝ, ∀ s : ℂ, tauL s = 0 → t₀ ≤ |s.im| →
    s.re ≤ 13 / 2 - c / Real.log |s.im|
theorem tauL_zero_free_region_left : ∃ c > 0, ∃ t₀ : ℝ, ∀ s : ℂ, tauL s = 0 → t₀ ≤ |s.im| →
    11 / 2 + c / Real.log |s.im| ≤ s.re
-- Uniform.lean
theorem tauL_zero_free_region_uniform : ∃ c > 0, ∀ s : ℂ, tauL s = 0 → (∀ n : ℕ, s ≠ -n) →
    s.re ≤ 13 / 2 - c / Real.log (|s.im| + 2) ∧ 11 / 2 + c / Real.log (|s.im| + 2) ≤ s.re
```

The uniform version covers every height, and it has no exceptional zero. Small heights are
handled as follows. The zeros with `|Im s| ≤ t₀` form a finite set (`ZeroCount.zeroSet_finite`).
Each of them has `11/2 < Re s < 13/2` by `EdgeNonvanishing`. The only real zeros of `tauL` are
the trivial zeros `0, −1, −2, …`, since `Λ(σ) > 0` for real `σ`. So no Siegel-type zero can occur.

In `tauL_zero_free_region` the constant is explicit: `c = 1/18144`. The height `t₀` is
`max(10, B, 2592)`, and `B` is ineffective. It comes from a compactness bound for `(z−1)ζ(z)` and
`(z−1)R(z)` near `z = 1`, the constant in `tauL_poly_bound`, and Rankin's `O(N^{3/5})` constant.

## Proof

Normalize `L(w) = tauL(w + 11/2)`, so the edge is `Re w = 1`. Let the zero be `ρ = β + iγ`, with
`η = 1 − β > 0` by edge non-vanishing. Let `F(σ)` be the positivity product of `EdgeNonvanishing`:
`ζ · L(·±iγ)² · (ζ(2·)R)² · ζ(2·±4iγ)R(·±2iγ)`, which is `L(Π×Π̃)` for
`Π = 1 ⊞ Δ|·|^{iγ} ⊞ Δ|·|^{−iγ}`.

1. **Continuation** (`Continuation`). This step applies Abel summation with an error term.
   - Suppose `|Σ_{n≤N} a(n) − cN| ≤ C N^θ`. Then `L(a,s) = cs/(s−1) + s∫_1^∞ E(t)t^{−s−1}dt`, with
     the integral holomorphic on `Re s > θ`. Holomorphy comes from Mathlib's
     `mellin_differentiableAt_of_isBigO_rpow`. The integral is bounded by `(C+‖c‖)/(Re s − θ)`.
   - For `a = 1` this gives `Z1 = (s−1)ζ(s)`, holomorphic on `Re s > 0`.
   - For `a(n) = τ(n)²/n¹¹` (Rankin, `θ = 3/5`) it gives `R1 = (s−1)R(s)` and `Rt = R(s)`,
     holomorphic on `Re s > 3/5` (`Rt` away from `s = 1`), with `‖Rt(s)‖ ≪ ‖s‖` away from `1`.
2. **The function** `Ψ = (z−1)³F(z)` (`Psi`).
   - It is holomorphic on `Ω = {Re > 3/5, |Im| < 1/2}`, and `Ψ(σ) = (σ−1)³F(σ)` for real `σ > 1`.
   - It is zero-free on `Re > 1`. This needs `R(s) ≠ 0` there, which is read off from `‖F‖ ≥ 1`.
   - It vanishes to order `≥ 4` at the real point `β`. Two factors come from `L(β+iγ) = 0` and
     two from `L(β−iγ) = 0` by conjugation.
   - It satisfies `‖Ψ‖ ≤ B(9+|γ|)^{10}` on `|z−(1+δ)| ≤ 1/4`. This uses `tauL_poly_bound`,
     `‖ζ(w)‖ ≤ Σ n^{−3/2}` for `Re w ≥ 3/2`, the `Rt` bound, and compactness.
3. **Sign** (`Monotone`, `re_logDeriv_Psi_le`). The Euler factor of `F` is `exp Σ_k a_k p^{−kσ}`
   with `a_k ≥ 0`. So `‖F(σ)‖` is non-increasing on `σ > 1` (`norm_Fval_antitone`). Then
   `‖Ψ(σ)‖²/(σ−1)⁶` is antitone. Its derivative at `1+δ` is therefore `≤ 0`, which gives
   `Re Ψ'/Ψ(1+δ) ≤ 3/δ`.
4. **Landau's lemma** (`Landau.landau`). Let `f` be analytic on `|z−c| ≤ r` with
   `|f| ≤ e^M|f(c)|`, and suppose every zero in `|z−c| ≤ r/3` has `Re ≤ Re c`. Then
   `−Re f'/f(c) ≤ 12M/r − m Re 1/(c−ρ₀)` for any zero `ρ₀` of order `≥ m` in that disc.
   - The zeros are extracted with Mathlib's `extract_zeros_poles`.
   - The quotient is bounded by the maximum principle on `|z−c| = 2r/3`.
   - The logarithm is built from Mathlib's `isExactOn_ball`.
   - The bound on its derivative uses Mathlib's `borelCaratheodory_zero` and the Cauchy estimate.
5. **Core** (`core`). Take `c = 1+δ`, `r = 1/4`, `m = 4`, `ρ₀ = β`, and use `‖Ψ(1+δ)‖ ≥ δ³`.
   This gives `4/(δ+η) ≤ 3/δ + 48 log(B(9+|γ|)^{10}/δ³)`. Then set `δ = 1/(2592 log|γ|)` and use
   `log(...) ≤ 27 log|γ|`. This gives `η ≥ 1/(18144 log|γ|)`.
6. **Left side.** Apply the functional equation `tauL(12−s) = 0`.

## Files

| file | content |
|---|---|
| `Landau.lean` | `norm_deriv_le_of_re_le` (Borel–Carathéodory + Cauchy at the centre), `landau` |
| `Continuation.lean` | `errE`, `abelI`, `norm_abelI_le`, `differentiableAt_abelI`, `LSeries_eq_abel`, `Z1`, `R1`, `Rt`, `norm_Rt_le` |
| `Monotone.lean` | `localD_inv_eq_exp_tsum`, `Fp_eq_localD`, `norm_Fp_antitone`, `norm_Fval_antitone`, `RS_ne_zero` |
| `Psi.lean` | `Ln`, `Psi`, `Om`, `differentiableOn_Psi`, `Psi_real`, `Psi_ne_zero`, `four_le_order`, `norm_Psi_le` |
| `Region.lean` | `re_logDeriv_Psi_le`, `core`, `tauL_zero_free_region`, `tauL_zero_free_region_left` |
| `Uniform.lean` | `tauL_zero_free_region_uniform` |
| `Main.lean` | `#print axioms` |

## Gaps and remarks

- **The constants are not effective.** `t₀` (and so the uniform `c`) depends on existential
  constants: Rankin's error constant, the convexity constant in `tauL_poly_bound`, and a
  compactness bound. The small-height part also uses finiteness rather than a numerical check.
- **No PNT corollary.** The prime number theorem for `τ`,
  `Σ_{p≤x} τ(p) log p ≪ x^{13/2} exp(−c√log x)`, would also need an explicit formula, or a
  Perron/contour argument with bounds for `L'/L` in the region. It is not done.
- **No Shimura.** Holomorphy of `L(Sym²Δ, s)` is not needed. Only `R(s) − cs/(s−1)` on
  `Re s > 3/5` (Rankin's error term) is used, as in `EdgeNonvanishing`.
- **Other forms.** The argument applies verbatim to any level-one Hecke eigenform for which
  `tauL_eulerProduct`, the Rankin error term and the polynomial growth bound are available. Only
  `Δ` is formalized here.

## Literature

- de la Vallée Poussin (1899); Landau, *Handbuch* (1909). For the GL(2) version via `L(f×f̄)`, see
  Iwaniec–Kowalski, *Analytic Number Theory*, Thm 5.10 and §5.3.
- Titchmarsh, *The Theory of the Riemann Zeta-Function*, §3.9 (Lemma α). Montgomery–Vaughan,
  *Multiplicative Number Theory I*, Lemmas 6.2–6.3 (Borel–Carathéodory, Landau).
- Rankin (1939), Ogg (1969), Moreno (1977): the positivity product.
