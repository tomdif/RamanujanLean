/-
# The additively twisted functional equation (GL(2) Voronoi input)

For `q ≥ 1` and integers `a, ā, b` with `a ā − b q = 1` (so `ā ≡ a⁻¹ mod q`), put

    F_x(t) = Δ(x + i t/q)    (t > 0),       L(Δ, x, s) = ∑ τ(n) e(nx) n^{−s}.

The matrix `γ = [[−ā, b], [q, −a]] ∈ SL₂(ℤ)` sends `a/q + it/q` to `−ā/q + i/(qt)` with
`q z − a = it`, so modularity gives

    F_{−ā/q}(1/t) = t¹² F_{a/q}(t)                          (`twF_inv`).

Hence `(F_{−ā/q}, F_{a/q})` is a Mathlib `StrongFEPair` of weight `12`, root number `1`, and with
`Λ(x, s) = ∫₀^∞ F_x(t) t^{s−1} dt`:

* `twLambda_entire`: `Λ(a/q, ·)` and `Λ(−ā/q, ·)` are entire;
* **`twLambda_functional_equation`**: `Λ(−ā/q, 12 − s) = Λ(a/q, s)` for all `s`;
* `twLambda_eq`: `Λ(x, s) = (2π/q)^{−s} Γ(s) L(Δ, x, s)` for `Re s > 7`.

So `L(Δ, a/q, s)` continues to an entire function with
`(q/2π)^{12−s}Γ(12−s) L(Δ,−ā/q,12−s) = (q/2π)^s Γ(s) L(Δ,a/q,s)`: the functional equation of
the additive twists, which is the input to the Voronoi summation formula
`∑ τ(n)e(an/q)w(n) = (1/q)∑ τ(n)e(−ān/q) ŵ(n/q²)` (Jutila's route to subconvexity).
-/
import RamanujanTau.HeckeL.Basic
import RamanujanTau.Subconvexity.Wilton

set_option autoImplicit false

namespace RamanujanTau.Subconvexity

open Complex ModularForm Filter Asymptotics Set MeasureTheory LSeries
open UpperHalfPlane hiding I
open scoped MatrixGroups Real
open RamanujanTau.RankinSelberg

local notation "𝕢" => Function.Periodic.qParam

/-- `F_x(t) = Δ(x + i t/q)` (junk for `t ≤ 0`). -/
noncomputable def twF (q x t : ℝ) : ℂ := (Δf ∘ ofComplex) ((x : ℂ) + ((t / q : ℝ) : ℂ) * I)

/-- The point `x + i t/q` of `ℍ`. -/
noncomputable def twPt {q t : ℝ} (hq : 0 < q) (ht : 0 < t) (x : ℝ) : ℍ :=
  ⟨(x : ℂ) + ((t / q : ℝ) : ℂ) * I, by simpa using div_pos ht hq⟩

lemma twPt_coe {q t : ℝ} (hq : 0 < q) (ht : 0 < t) (x : ℝ) :
    ((twPt hq ht x : ℍ) : ℂ) = (x : ℂ) + ((t / q : ℝ) : ℂ) * I := rfl

lemma twPt_im {q t : ℝ} (hq : 0 < q) (ht : 0 < t) (x : ℝ) : (twPt hq ht x).im = t / q := by
  show ((x : ℂ) + ((t / q : ℝ) : ℂ) * I).im = t / q
  simp

lemma twF_eq {q t : ℝ} (hq : 0 < q) (ht : 0 < t) (x : ℝ) : twF q x t = Δf (twPt hq ht x) := by
  unfold twF
  simp only [Function.comp_apply]
  congr 1
  rw [ofComplex_apply_of_im_pos (by simpa using div_pos ht hq)]
  rfl

lemma continuousOn_twF {q : ℝ} (hq : 0 < q) (x : ℝ) : ContinuousOn (twF q x) (Ioi 0) := by
  have hd := UpperHalfPlane.mdifferentiable_iff.mp
    (ModularFormClass.holo (CuspForm.discriminant : CuspForm 𝒮ℒ 12))
  have hc : ContinuousOn (fun t : ℝ => (x : ℂ) + ((t / q : ℝ) : ℂ) * I) (Ioi 0) := by
    apply Continuous.continuousOn; fun_prop
  exact hd.continuousOn.comp hc fun t ht => by simpa using div_pos ht hq

lemma locallyIntegrableOn_twF {q : ℝ} (hq : 0 < q) (x : ℝ) :
    LocallyIntegrableOn (twF q x) (Ioi 0) :=
  (continuousOn_twF hq x).locallyIntegrableOn measurableSet_Ioi

/-- Exponential decay: `‖Δ(x + it/q)‖ ≤ C e^{−2πt/q}` eventually. -/
lemma twF_isBigO_exp {q : ℝ} (hq : 0 < q) (x : ℝ) :
    twF q x =O[atTop] fun t => Real.exp (-(2 * π / q) * t) := by
  have hdec := CuspFormClass.exp_decay_atImInfty (Γ := 𝒮ℒ) (k := 12)
    (CuspForm.discriminant : CuspForm 𝒮ℒ 12) one_pos one_mem_strictPeriods_SL
  obtain ⟨C, hC⟩ := hdec.bound
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hC
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop (q * max A 1)] with t htA
  have hq1 : 0 < q * max A 1 := mul_pos hq (by positivity)
  have ht : 0 < t := lt_of_lt_of_le hq1 htA
  have him : A ≤ t / q := by
    rw [le_div_iff₀ hq]
    calc A * q ≤ max A 1 * q := by gcongr; exact le_max_left _ _
      _ = q * max A 1 := by ring
      _ ≤ t := htA
  have hb := hA (twPt hq ht x) (by rw [twPt_im]; exact him)
  simp only [Set.mem_setOf_eq, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), twPt_im,
    div_one] at hb
  rw [twF_eq hq ht, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  convert hb using 3; ring

lemma twF_top {q : ℝ} (hq : 0 < q) (x : ℝ) (r : ℝ) : twF q x =O[atTop] (· ^ r) :=
  (twF_isBigO_exp hq x).trans (isLittleO_exp_neg_mul_rpow_atTop (by positivity) r).isBigO

/-! ## The modular relation -/

/-- The matrix `[[−ā, b], [q, −a]] ∈ SL₂(ℤ)`. -/
def gam (q a abar b : ℤ) (h : a * abar - b * q = 1) : SL(2, ℤ) :=
  ⟨!![-abar, b; q, -a], by rw [Matrix.det_fin_two_of]; linear_combination h⟩

/-- **The modular relation**: `F_{−ā/q}(1/t) = t¹² F_{a/q}(t)`. -/
theorem twF_inv {q : ℕ} (hq : 0 < q) (a abar b : ℤ) (h : a * abar - b * q = 1) {t : ℝ}
    (ht : 0 < t) :
    twF q (-(abar : ℝ) / q) (1 / t) = (t : ℂ) ^ 12 * twF q ((a : ℝ) / q) t := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  set z : ℍ := twPt hqR ht ((a : ℝ) / q)
  set γ := gam q a abar b h
  have hmem : ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have hD := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hmem z
  have hden : denom ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) z = (t : ℂ) * I := by
    simp only [denom, γ, gam, twPt_coe, z]
    simp
    field_simp
    ring
  have hval : (γ • z : ℍ) = twPt hqR (one_div_pos.mpr ht) (-(abar : ℝ) / q) := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_specialLinearGroup_apply, twPt_coe, twPt_coe]
    simp only [γ, gam]
    simp
    have hden' : (q : ℂ) * ((a : ℂ) / q + (t : ℂ) / q * I) + -(a : ℂ) = (t : ℂ) * I := by
      field_simp; ring
    rw [hden']
    have hI : (t : ℂ) * I ≠ 0 := mul_ne_zero htC I_ne_zero
    rw [div_eq_iff hI]
    have hC : (a : ℂ) * abar - b * q = 1 := by exact_mod_cast h
    field_simp
    ring_nf
    rw [I_sq]
    linear_combination (-1 : ℂ) * hC
  rw [twF_eq hqR (one_div_pos.mpr ht), twF_eq hqR ht, ← hval]
  have hs : ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) • z = γ • z := rfl
  rw [hs, hden] at hD
  show CuspForm.discriminant (γ • z) = (t : ℂ) ^ 12 * CuspForm.discriminant z
  rw [hD]
  congr 1
  rw [show ((12 : ℤ)) = ((12 : ℕ) : ℤ) by rfl, zpow_natCast, mul_pow,
    show (12 : ℕ) = 4 * 3 by rfl, pow_mul I, I_pow_four]
  simp

/-! ## The strong FE pair and the completed twisted L-function -/

/-- **The strong functional-equation pair** `(F_{−ā/q}, F_{a/q})`, weight `12`, root number `1`. -/
noncomputable def twPair {q : ℕ} (hq : 0 < q) (a abar b : ℤ) (h : a * abar - b * q = 1) :
    StrongFEPair ℂ where
  f := twF q (-(abar : ℝ) / q)
  g := twF q ((a : ℝ) / q)
  k := 12
  ε := 1
  f₀ := 0
  g₀ := 0
  hf_int := locallyIntegrableOn_twF (by exact_mod_cast hq) _
  hg_int := locallyIntegrableOn_twF (by exact_mod_cast hq) _
  hk := by norm_num
  hε := one_ne_zero
  h_feq := fun x hx => by
    rw [twF_inv hq a abar b h hx, one_mul, smul_eq_mul,
      show (12:ℝ) = ((12:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    push_cast; rfl
  hf_top := fun r => by simpa using twF_top (by exact_mod_cast hq) _ r
  hg_top := fun r => by simpa using twF_top (by exact_mod_cast hq) _ r
  hf₀ := rfl
  hg₀ := rfl

/-- **The completed additively twisted L-function** `Λ(x, s) = ∫₀^∞ Δ(x + it/q) t^{s−1} dt`. -/
noncomputable def twLambda (q x : ℝ) : ℂ → ℂ := mellin (twF q x)

/-- `Λ(a/q, ·)` and `Λ(−ā/q, ·)` are entire. -/
theorem twLambda_entire {q : ℕ} (hq : 0 < q) (a abar b : ℤ) (h : a * abar - b * q = 1) :
    Differentiable ℂ (twLambda q ((a : ℝ) / q)) ∧
      Differentiable ℂ (twLambda q (-(abar : ℝ) / q)) :=
  ⟨(twPair hq a abar b h).symm.differentiable_Λ, (twPair hq a abar b h).differentiable_Λ⟩

/-- **Functional equation of the additive twists**: `Λ(−ā/q, 12 − s) = Λ(a/q, s)`. -/
theorem twLambda_functional_equation {q : ℕ} (hq : 0 < q) (a abar b : ℤ)
    (h : a * abar - b * q = 1) (s : ℂ) :
    twLambda q (-(abar : ℝ) / q) (12 - s) = twLambda q ((a : ℝ) / q) s := by
  have H := (twPair hq a abar b h).functional_equation s
  have hk : (((twPair hq a abar b h).k : ℝ) : ℂ) = 12 := by simp [twPair]
  rw [hk] at H
  have e1 : twLambda q (-(abar : ℝ) / q) (12 - s) = (twPair hq a abar b h).Λ (12 - s) := rfl
  rw [e1, H]
  show (1 : ℂ) • mellin (twF q ((a : ℝ) / q)) s = _
  rw [one_smul]; rfl

/-! ## The Mellin transform is the twisted Dirichlet series -/

/-- The twisted coefficients `τ(n) e(nx)`. -/
noncomputable def twC (x : ℝ) (n : ℕ) : ℂ := ((tau n : ℤ) : ℂ) * eC (n * x)

lemma twC_zero (x : ℝ) : twC x 0 = 0 := by simp [twC, tau_zero]

lemma norm_twC (x : ℝ) (n : ℕ) : ‖twC x n‖ = ‖tauC n‖ := by
  rw [twC, norm_mul, norm_eC, mul_one]; rfl

lemma LSeriesSummable_twC (x : ℝ) {s : ℂ} (hs : 7 < s.re) : LSeriesSummable (twC x) s := by
  have hL := (LSeriesSummable_tau hs).norm
  refine Summable.of_norm_bounded hL fun n => le_of_eq ?_
  rw [norm_term_eq, norm_term_eq, norm_twC]

/-- `Δ(x + it/q) = ∑ τ(n) e(nx) e^{−2πnt/q}`. -/
lemma hasSum_twF {q : ℝ} (hq : 0 < q) (x : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => twC x n * (Real.exp (-(2 * π * n / q) * t) : ℂ)) (twF q x t) := by
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex
    (CuspForm.discriminant : CuspForm 𝒮ℒ 12) one_mem_strictPeriods_SL
  have H := hasSum_qExpansion one_pos hper
    (ModularFormClass.holo (CuspForm.discriminant : CuspForm 𝒮ℒ 12))
    (ModularFormClass.bdd_at_infty (CuspForm.discriminant : CuspForm 𝒮ℒ 12)) (twPt hq ht x)
  rw [twF_eq hq ht]
  refine H.congr_fun fun n => ?_
  rw [TauBound.qExpansion_discriminant_coeff_tau, smul_eq_mul, twC, mul_assoc]
  congr 1
  unfold Function.Periodic.qParam eC
  rw [twPt_coe, Complex.ofReal_exp, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- **The Mellin transform of `Δ(x + it/q)`**: `(2π/q)^{−s} Γ(s) L(Δ, x, s)` for `Re s > 7`. -/
theorem twLambda_eq {q : ℝ} (hq : 0 < q) (x : ℝ) {s : ℂ} (hs : 7 < s.re) :
    twLambda q x s = ((2 * π / q : ℝ) : ℂ) ^ (-s) * Gamma s * LSeries (twC x) s := by
  have hs0 : 0 < s.re := by linarith
  have hc : (0 : ℝ) < 2 * π / q := by positivity
  have hpn : ∀ n : ℕ, 2 * π * n / q = (2 * π / q) * n := fun n => by ring
  have hp : ∀ n : ℕ, twC x n = 0 ∨ 0 < 2 * π * n / q := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact Or.inl (twC_zero x)
    · exact Or.inr (by positivity)
  have hsum : Summable fun n : ℕ => ‖twC x n‖ / (2 * π * n / q) ^ s.re := by
    have hL := (LSeriesSummable_twC x hs).norm
    refine (hL.mul_left ((2 * π / q) ^ (-s.re))).congr fun n => ?_
    rw [norm_term_eq]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [twC_zero]
    · rw [if_neg hn.ne', hpn, Real.mul_rpow hc.le (Nat.cast_nonneg n), Real.rpow_neg hc.le]
      field_simp
  have H := hasSum_mellin hp hs0 (fun t ht => hasSum_twF hq x ht) hsum
  have H2 : HasSum (fun n => Gamma s * twC x n / ((2 * π * n / q : ℝ) : ℂ) ^ s)
      (((2 * π / q : ℝ) : ℂ) ^ (-s) * Gamma s * LSeries (twC x) s) := by
    have hL := (LSeriesSummable_twC x hs).LSeriesHasSum.mul_left
      (((2 * π / q : ℝ) : ℂ) ^ (-s) * Gamma s)
    refine hL.congr_fun fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [twC_zero]
    · rw [term_of_ne_zero hn.ne', hpn, Complex.ofReal_mul,
        mul_cpow_ofReal_nonneg hc.le (Nat.cast_nonneg n), cpow_neg]
      push_cast
      ring
  exact H.unique H2

/-! ## Small-denominator twists: smooth sums are exponentially small -/

/-- Cusp decay `‖Δ(p)‖ ≤ A e^{−2π Im p}` for `Im p ≥ Y`. -/
lemma delta_cusp_bound : ∃ A Y : ℝ, 0 ≤ A ∧ 0 < Y ∧
    ∀ p : ℍ, Y ≤ p.im → ‖Δf p‖ ≤ A * Real.exp (-(2 * π) * p.im) := by
  have hdec := CuspFormClass.exp_decay_atImInfty (Γ := 𝒮ℒ) (k := 12)
    (CuspForm.discriminant : CuspForm 𝒮ℒ 12) one_pos one_mem_strictPeriods_SL
  obtain ⟨C, hC⟩ := hdec.bound
  obtain ⟨Y, hY⟩ := (atImInfty_mem _).mp hC
  refine ⟨max C 0, max Y 1, le_max_right _ _, by positivity, fun p hp => ?_⟩
  have hb := hY p ((le_max_left _ _).trans hp)
  simp only [Set.mem_setOf_eq, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), div_one] at hb
  have e : -2 * π * p.im = -(2 * π) * p.im := by ring
  rw [e] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)

/-- **Smooth sums with a small-denominator rational twist are exponentially small.**
For `a ā ≡ 1 (mod q)` and `y > 0` with `1/(q²y) ≥ Y`,

    ∑ τ(n) e(an/q) e^{−2πny} = Δ(a/q + iy),   ‖Δ(a/q + iy)‖ ≤ A (qy)^{−12} e^{−2π/(q²y)}.

In normalized terms: a smooth sum of length `X = 1/y` twisted by `e(an/q)` with `q ≤ X^{1/2−ε}`
is `O_A(X^{−A})`, uniformly in `a`.  This is the "major arc" input to Jutila's method. -/
theorem smooth_twist_decay : ∃ A Y : ℝ, 0 ≤ A ∧ 0 < Y ∧
    ∀ (q : ℕ) (hq : 0 < q) (a abar b : ℤ) (_ : a * abar - b * q = 1) (y : ℝ) (hy : 0 < y),
      Y ≤ 1 / ((q : ℝ) ^ 2 * y) →
      HasSum (fun n : ℕ => twC ((a : ℝ) / q) n * (Real.exp (-(2 * π * n) * y) : ℂ))
          (twF q ((a : ℝ) / q) (q * y)) ∧
      ‖twF q ((a : ℝ) / q) (q * y)‖ ≤
          A * ((q : ℝ) * y) ^ (-12 : ℤ) * Real.exp (-(2 * π) * (1 / ((q : ℝ) ^ 2 * y))) := by
  obtain ⟨A, Y, hA, hY, hb⟩ := delta_cusp_bound
  refine ⟨A, Y, hA, hY, fun q hq a abar b h y hy hYy => ⟨?_, ?_⟩⟩
  · have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have H := hasSum_twF hqR ((a : ℝ) / q) (mul_pos hqR hy)
    refine H.congr_fun fun n => ?_
    congr 3
    field_simp
  · have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have ht : 0 < (q : ℝ) * y := mul_pos hqR hy
    have hinv := twF_inv hq a abar b h ht
    have hT : (((q : ℝ) * y : ℝ) : ℂ) ^ 12 ≠ 0 := pow_ne_zero _ (by exact_mod_cast ht.ne')
    have hF : twF q ((a : ℝ) / q) (q * y) =
        ((((q : ℝ) * y : ℝ) : ℂ) ^ 12)⁻¹ * twF q (-(abar : ℝ) / q) (1 / (q * y)) := by
      rw [hinv, ← mul_assoc, inv_mul_cancel₀ hT, one_mul]
    have hpos : 0 < 1 / ((q : ℝ) * y) := one_div_pos.mpr ht
    have him : (twPt hqR hpos (-(abar : ℝ) / q)).im = 1 / ((q : ℝ) ^ 2 * y) := by
      rw [twPt_im]; field_simp
    have hB := hb (twPt hqR hpos (-(abar : ℝ) / q)) (by rw [him]; exact hYy)
    rw [him] at hB
    rw [hF, norm_mul, twF_eq hqR hpos, norm_inv, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht]
    rw [show ((q : ℝ) * y) ^ (-12 : ℤ) = (((q : ℝ) * y) ^ 12)⁻¹ by
      rw [zpow_neg, show ((12 : ℤ)) = ((12 : ℕ) : ℤ) by rfl, zpow_natCast]]
    calc (((q : ℝ) * y) ^ 12)⁻¹ * ‖Δf (twPt hqR hpos (-(abar : ℝ) / q))‖
        ≤ (((q : ℝ) * y) ^ 12)⁻¹ * (A * Real.exp (-(2 * π) * (1 / ((q : ℝ) ^ 2 * y)))) :=
          mul_le_mul_of_nonneg_left hB (by positivity)
      _ = _ := by ring

end RamanujanTau.Subconvexity
