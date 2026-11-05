/-
# Sign changes of real cusp-form coefficients via Landau's theorem

For every nonzero `f ∈ S_k(SL₂(ℤ))` with real q-coefficients `a(n)`, both `a(n) > 0` and
`a(n) < 0` hold for infinitely many `n`.

Proof: if `u · a(n) ≥ 0` for all `n ≥ M` (`u = ±1`), the truncated sequence
`b(n) = [n ≥ M] u a(n)` is nonnegative, and its L-series is `u (L(f,s) − Σ_{n<M} a(n) n^{-s})`
on `Re s > (k+1)/2`, which has the entire continuation `u (fL f s − Σ_{n<M} a(n) n^{-s})`.
Landau's theorem (`RamanujanTau.LandauSigns.landau`) gives absolute convergence at `s = 0`, so
`a(n) → 0`, contradicting `RamanujanTau.TauOmega.coeff_omega` (`|a(n)| ≥ c n^{(k-1)/2}` i.o.).
-/
import RamanujanTau.LandauSigns.Landau
import RamanujanTau.HeckeConvexGeneral.Main
import RamanujanTau.TauOmega.General

set_option autoImplicit false

namespace RamanujanTau.LandauSigns

open Complex LSeries Filter Finset ModularForm
open UpperHalfPlane hiding I
open RamanujanTau.HeckeConvexGeneral
open scoped ComplexOrder MatrixGroups

/-! ## Truncated, twisted coefficient sequences -/

/-- `n ↦ [n ≥ M] · u · g(n)`. -/
noncomputable def trunc (g : ℕ → ℂ) (u : ℂ) (M : ℕ) (n : ℕ) : ℂ := if n < M then 0 else u * g n

lemma term_trunc (g : ℕ → ℂ) (u : ℂ) (M : ℕ) (s : ℂ) (n : ℕ) :
    term (trunc g u M) s n = u * term g s n - (if n < M then u * term g s n else 0) := by
  simp only [term_def, trunc]
  split_ifs <;> ring

lemma summable_trunc_aux (g : ℕ → ℂ) (u : ℂ) (M : ℕ) (s : ℂ) :
    HasSum (fun n => if n < M then u * term g s n else 0) (∑ n ∈ range M, u * term g s n) := by
  convert hasSum_sum_of_ne_finset_zero (s := range M)
    (f := fun n => if n < M then u * term g s n else 0)
    (fun n hn => if_neg (by simpa using hn)) using 1
  · exact Finset.sum_congr rfl fun n hn => (if_pos (by simpa using hn)).symm
  · infer_instance

lemma LSeriesSummable_trunc {g : ℕ → ℂ} {s : ℂ} (hg : LSeriesSummable g s) (u : ℂ) (M : ℕ) :
    LSeriesSummable (trunc g u M) s := by
  unfold LSeriesSummable
  rw [show term (trunc g u M) s = _ from funext (term_trunc g u M s)]
  exact (hg.mul_left u).sub (summable_trunc_aux g u M s).summable

lemma LSeries_trunc {g : ℕ → ℂ} {s : ℂ} (hg : LSeriesSummable g s) (u : ℂ) (M : ℕ) :
    LSeries (trunc g u M) s = u * (LSeries g s - ∑ n ∈ range M, term g s n) := by
  unfold LSeries
  rw [show term (trunc g u M) s = _ from funext (term_trunc g u M s),
    ((hg.mul_left u).hasSum.sub (summable_trunc_aux g u M s)).tsum_eq, tsum_mul_left,
    mul_sub, Finset.mul_sum]

lemma differentiable_term (g : ℕ → ℂ) (n : ℕ) : Differentiable ℂ (fun s => term g s n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [term_zero]; exact differentiable_const 0
  · have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    simp only [term_of_ne_zero hn]
    exact (differentiable_const _).div (differentiable_id.const_cpow (Or.inl hn'))
      fun s => (cpow_eq_zero_iff _ _).not.mpr fun h => hn' h.1

/-! ## The core contradiction -/

variable {k : ℕ}

/-- A nonzero level-one cusp form has weight `k ≥ 12`, in particular `k ≥ 1`. -/
lemma twelve_le_weight {f : CuspForm 𝒮ℒ (k : ℤ)} (hf : f ≠ 0) : 12 ≤ k := by
  by_contra h
  exact hf (rank_zero_iff_forall_zero.mp
    (CuspForm.rank_eq_zero_of_weight_lt_twelve (k := (k : ℤ)) (by omega)) f)

/-- **Core.** For `f ≠ 0` and any `u ≠ 0`, the sequence `u · a_f(n)` is *not* eventually
nonnegative (in `ComplexOrder`, i.e. real and `≥ 0`). -/
theorem not_eventually_nonneg (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) {u : ℂ} (hu : u ≠ 0)
    (M : ℕ) : ¬ ∀ n, M ≤ n → 0 ≤ u * coef f n := by
  intro hpos
  have hk : 1 ≤ k := le_trans (by norm_num) (twelve_le_weight hf)
  set x : ℝ := ((k : ℝ) + 1) / 2 with hx_def
  -- nonnegativity of the truncated sequence
  have ha : 0 ≤ trunc (coef f) u M := by
    intro n
    simp only [trunc, Pi.zero_apply]
    split_ifs with h
    · exact le_rfl
    · exact hpos n (not_lt.mp h)
  -- the entire continuation
  have hF : Differentiable ℂ
      (fun s => u * (fL f s - ∑ n ∈ range M, term (coef f) s n)) :=
    (differentiable_const u).mul ((fL_entire f hk).sub
      (Differentiable.fun_sum fun n _ => differentiable_term (coef f) n))
  have hEq : {s : ℂ | x < s.re}.EqOn
      (fun s => u * (fL f s - ∑ n ∈ range M, term (coef f) s n)) (LSeries (trunc (coef f) u M)) := by
    intro s hs
    simp only [Set.mem_setOf_eq] at hs
    simp only
    rw [LSeries_trunc (LSeriesSummable_coef f hk hs), fL_eq_LSeries f hk hs]
  have hx : abscissaOfAbsConv (trunc (coef f) u M) ≤ x :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      LSeriesSummable_trunc (LSeriesSummable_coef f hk (by simpa using hy)) u M
  -- Landau: absolute convergence at `s = 0`
  have h0 := landau ha hF hx hEq 0
  have htend := h0.tendsto_atTop_zero.norm
  simp only [norm_zero] at htend
  obtain ⟨c, hc, hom⟩ := RamanujanTau.TauOmega.coeff_omega f hf hk
  have hcu : 0 < ‖u‖ * c := mul_pos (norm_pos_iff.mpr hu) hc
  obtain ⟨N, hN⟩ := eventually_atTop.mp (htend.eventually (gt_mem_nhds hcu))
  obtain ⟨n, hn, hbig⟩ := hom (max (max M 1) N)
  have hnM : M ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn1 : 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnN : N ≤ n := le_trans (le_max_right _ _) hn
  have hlt := hN n hnN
  have hn0 : n ≠ 0 := by omega
  rw [term_of_ne_zero hn0, cpow_zero, div_one, trunc, if_neg (by omega), norm_mul] at hlt
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ (((k : ℝ) - 1) / 2) :=
    Real.one_le_rpow (by exact_mod_cast hn1)
      (div_nonneg (sub_nonneg.mpr (by exact_mod_cast hk)) (by norm_num))
  have hc' : c ≤ ‖coef f n‖ := le_trans (le_mul_of_one_le_right hc.le hpow) hbig
  have := mul_le_mul_of_nonneg_left hc' (norm_nonneg u)
  linarith

/-! ## Headline: infinitely many sign changes -/

/-- **Positive coefficients infinitely often.** -/
theorem coeff_pos_infinitely_often (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0)
    (hreal : ∀ n, ((qExpansion 1 f).coeff n).im = 0) :
    ∀ M : ℕ, ∃ n, M ≤ n ∧ 0 < ((qExpansion 1 f).coeff n).re := by
  intro M
  by_contra h
  push Not at h
  refine not_eventually_nonneg f hf (u := -1) (by norm_num) M fun n hn => ?_
  rw [neg_one_mul, Complex.nonneg_iff]
  refine ⟨?_, ?_⟩
  · simp only [neg_re]; exact neg_nonneg.mpr (h n hn)
  · simp only [neg_im]; rw [show (coef f n).im = 0 from hreal n]; simp

/-- **Negative coefficients infinitely often.** -/
theorem coeff_neg_infinitely_often (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0)
    (hreal : ∀ n, ((qExpansion 1 f).coeff n).im = 0) :
    ∀ M : ℕ, ∃ n, M ≤ n ∧ ((qExpansion 1 f).coeff n).re < 0 := by
  intro M
  by_contra h
  push Not at h
  refine not_eventually_nonneg f hf (u := 1) one_ne_zero M fun n hn => ?_
  rw [one_mul, Complex.nonneg_iff]
  exact ⟨h n hn, (hreal n).symm⟩

/-- **Landau sign-change theorem** for real level-one cusp forms. -/
theorem coeff_sign_changes (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0)
    (hreal : ∀ n, ((qExpansion 1 f).coeff n).im = 0) :
    (∀ M : ℕ, ∃ n, M ≤ n ∧ 0 < ((qExpansion 1 f).coeff n).re) ∧
    (∀ M : ℕ, ∃ n, M ≤ n ∧ ((qExpansion 1 f).coeff n).re < 0) :=
  ⟨coeff_pos_infinitely_often f hf hreal, coeff_neg_infinitely_often f hf hreal⟩

/-! ## The `τ` specialization -/

lemma discriminant_ne_zero' : (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ)) ≠ 0 := by
  intro h
  have := congrArg (fun g : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ) => (g : UpperHalfPlane → ℂ)
    UpperHalfPlane.I) h
  simp only [CuspForm.zero_apply] at this
  exact ModularForm.discriminant_ne_zero _ this

/-- **`τ(n) > 0` and `τ(n) < 0` each for infinitely many `n`** (via Landau). -/
theorem tau_sign_changes :
    (∀ M : ℕ, ∃ n, M ≤ n ∧ 0 < RamanujanTau.tau n) ∧
    (∀ M : ℕ, ∃ n, M ≤ n ∧ RamanujanTau.tau n < 0) := by
  have hc : ∀ n, (qExpansion 1 (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ))).coeff n =
      ((RamanujanTau.tau n : ℤ) : ℂ) := fun n => coef_discriminant n
  have hreal : ∀ n, ((qExpansion 1
      (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ))).coeff n).im = 0 := by
    intro n; rw [hc]; simp
  obtain ⟨hp, hn⟩ := coeff_sign_changes _ discriminant_ne_zero' hreal
  refine ⟨fun M => ?_, fun M => ?_⟩
  · obtain ⟨n, hM, h⟩ := hp M
    rw [hc] at h
    exact ⟨n, hM, by exact_mod_cast (by simpa using h)⟩
  · obtain ⟨n, hM, h⟩ := hn M
    rw [hc] at h
    exact ⟨n, hM, by exact_mod_cast (by simpa using h)⟩

end RamanujanTau.LandauSigns
