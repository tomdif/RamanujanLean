/-
# Mean square of `S(x) = ∑_{n≤x} τ(n)` at the critical exponent `25/2`

* `tau_mean_square_convergent`: `∫₁^∞ S(x)² x^{−2σ−1} dx < ∞` for every `σ > 23/4`;
* `tau_mean_square_mellin`: `c/δ ≤ ∫₁^∞ S(x)² x^{−25/2−2δ} dx ≤ C/δ` for `0 < δ ≤ 1/16`;
* `tau_log_mean_square`: `c log X ≤ ∫₁^X S(x)² x^{−25/2} dx ≤ C log X` for `X ≥ X₀`;
* `tau_mean_square_upper`: `∫₁^X S(x)² dx ≤ C X^{25/2} log X`;
* `tau_mean_square_omega`: `∫₁^X S(x)² dx ≥ c X^{25/2}` for arbitrarily large `X`.
-/
import RamanujanTau.Voronoi.Bounds

set_option autoImplicit false

namespace RamanujanTau.Voronoi

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.HeckeL RamanujanTau.HeckeConvexGeneral RamanujanTau.TauOmegaPartial
open scoped ComplexConjugate Real MatrixGroups Interval

/-- `S(x) = ∑_{1≤n≤x} τ(n)`. -/
noncomputable def S (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (tau n : ℝ)

lemma gsq_eq (x : ℝ) : gsq x = S x ^ 2 := by
  have e : A Dl x = ((S x : ℝ) : ℂ) := by
    rw [A, S]; simp_rw [coef_discriminant]; push_cast; rfl
  rw [gsq, e, Complex.norm_real, Real.norm_eq_abs, sq_abs]

lemma measurable_S : Measurable S := by
  have h : S = (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (tau n : ℝ)) ∘ (fun x : ℝ => ⌊x⌋₊) := rfl
  rw [h]; exact (measurable_from_nat).comp Nat.measurable_floor

lemma S_of_lt_one {x : ℝ} (hx : x < 1) : S x = 0 := by
  have : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr hx
  simp [S, this]

/-- `h_σ(x) = S(x)² x^{−2σ−1}`. -/
noncomputable def hR (σ x : ℝ) : ℝ := S x ^ 2 * x ^ (-2 * σ - 1)

lemma hR_nonneg (σ : ℝ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ hR σ x := by
  unfold hR; have := Real.rpow_nonneg hx (-2 * σ - 1); positivity

lemma measurable_hR (σ : ℝ) : Measurable (hR σ) :=
  (measurable_S.pow_const 2).mul (measurable_id.pow_const _)

lemma mellin_integrand_eq (σ : ℝ) {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ (-(((2 * σ : ℝ)) : ℂ) - 1) • gC t = ((hR σ t : ℝ) : ℂ) := by
  rw [gC, gsq_eq, hR, smul_eq_mul]
  have e : -(((2 * σ : ℝ)) : ℂ) - 1 = (((-2 * σ - 1 : ℝ)) : ℂ) := by push_cast; ring
  rw [e, ← Complex.ofReal_cpow ht.le]
  push_cast; ring

/-- Mellin convergence at `−2σ` is integrability of `S² x^{−2σ−1}` on `(1, ∞)`, and the Mellin
value is the real integral. -/
lemma mellin_real (σ : ℝ) (hc : MellinConvergent gC (-(((2 * σ : ℝ)) : ℂ))) :
    IntegrableOn (hR σ) (Ioi 1) ∧
      mellin gC (-(((2 * σ : ℝ)) : ℂ)) = ((∫ x in Ioi (1 : ℝ), hR σ x : ℝ) : ℂ) := by
  have hcongr : EqOn (fun t : ℝ => (t : ℂ) ^ (-(((2 * σ : ℝ)) : ℂ) - 1) • gC t)
      (fun t => ((hR σ t : ℝ) : ℂ)) (Ioi 0) := fun t ht => mellin_integrand_eq σ ht
  have hi0 : IntegrableOn (fun t => ((hR σ t : ℝ) : ℂ)) (Ioi 0) :=
    (integrableOn_congr_fun hcongr measurableSet_Ioi).1 hc
  have hiR : IntegrableOn (hR σ) (Ioi 0) := by
    have := hi0.re
    simpa using this
  refine ⟨hiR.mono_set (Ioi_subset_Ioi zero_le_one), ?_⟩
  rw [mellin, setIntegral_congr_fun measurableSet_Ioi hcongr, integral_complex_ofReal]
  congr 1
  refine setIntegral_eq_of_subset_of_ae_diff_eq_zero measurableSet_Ioi.nullMeasurableSet
    (Ioi_subset_Ioi zero_le_one) ?_
  have h1 : ∀ᵐ x : ℝ ∂volume, x ∈ ({1} : Set ℝ)ᶜ :=
    compl_mem_ae_iff.mpr (measure_singleton 1)
  filter_upwards [h1] with x hx1 hx
  have hx1' : x ≠ 1 := hx1
  rcases hx with ⟨_, h2⟩
  simp only [mem_Ioi, not_lt] at h2
  have : x < 1 := lt_of_le_of_ne h2 hx1'
  rw [hR, S_of_lt_one this]; ring

/-- **Convergence of the critical mean square** for every `σ > 23/4`. -/
theorem tau_mean_square_convergent {σ : ℝ} (hσ : 23 / 4 < σ) :
    IntegrableOn (fun x : ℝ => S x ^ 2 * x ^ (-2 * σ - 1)) (Ioi 1) :=
  (mellin_real σ (mc_all (2 * σ) (by linarith))).1

lemma integral_hR_eq {σ : ℝ} (h1 : 23 / 4 < σ) (h2 : σ < 6) :
    ∫ x in Ioi (1 : ℝ), hR σ x = ∫ ξ : ℝ, ‖Fs Dl σ ξ‖ ^ 2 := by
  obtain ⟨hc, he⟩ := mellin_sq h1 h2
  have h := (mellin_real σ hc).2
  rw [he] at h
  exact_mod_cast h.symm

/-- **Two-sided Mellin mean square**: `∫₁^∞ S(x)² x^{−25/2−2δ} dx ≍ 1/δ`. -/
theorem tau_mean_square_mellin : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 16 →
    c / δ ≤ ∫ x in Ioi (1 : ℝ), S x ^ 2 * x ^ (-(25 / 2) - 2 * δ) ∧
      ∫ x in Ioi (1 : ℝ), S x ^ 2 * x ^ (-(25 / 2) - 2 * δ) ≤ C / δ := by
  obtain ⟨C, hC0, hC⟩ := Phi_upper
  obtain ⟨K2, hK2, hK⟩ := Phi_lower
  refine ⟨K2 / 4, C + 1, by positivity, by positivity, fun δ hδ0 hδ1 => ?_⟩
  have e : ∀ x : ℝ, S x ^ 2 * x ^ (-(25 / 2) - 2 * δ) = hR (23 / 4 + δ) x := by
    intro x; rw [hR]; congr 2; ring
  simp_rw [e]
  rw [integral_hR_eq (by linarith) (by linarith)]
  refine ⟨?_, ?_⟩
  · have := hK δ hδ0 hδ1
    calc K2 / 4 / δ = K2 / (4 * δ) := by rw [div_div]
      _ ≤ _ := this
  · refine (hC δ hδ0 hδ1).2.trans ?_
    gcongr; linarith

/-! ### From the Mellin mean square to `∫₁^X` -/

/-- `ψ(x) = S(x)² x^{−25/2}`. -/
noncomputable def psiR (x : ℝ) : ℝ := S x ^ 2 * x ^ (-(25 / 2 : ℝ))

lemma psiR_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ psiR x := by
  unfold psiR; have := Real.rpow_nonneg hx (-(25 / 2 : ℝ)); positivity

lemma measurable_psiR : Measurable psiR :=
  (measurable_S.pow_const 2).mul (measurable_id.pow_const _)

lemma intOn_phi {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun x : ℝ => S x ^ 2 * x ^ (-(25 / 2) - 2 * δ)) (Ioi 1) := by
  have h := tau_mean_square_convergent (σ := 23 / 4 + δ) (by linarith)
  have e : (-2 * (23 / 4 + δ) - 1 : ℝ) = -(25 / 2) - 2 * δ := by ring
  rw [e] at h; exact h

/-- `x^{−25/2} ≤ X^{2δ} x^{−25/2−2δ}` for `0 < x ≤ X`. -/
lemma rpow_shift_le {x X δ : ℝ} (hx : 0 < x) (hxX : x ≤ X) (hδ : 0 ≤ δ) :
    x ^ (-(25 / 2 : ℝ)) ≤ X ^ (2 * δ) * x ^ (-(25 / 2) - 2 * δ) := by
  have e : x ^ (-(25 / 2 : ℝ)) = x ^ (2 * δ) * x ^ (-(25 / 2) - 2 * δ) := by
    rw [← Real.rpow_add hx]; congr 1; ring
  rw [e]
  have := Real.rpow_pos_of_pos hx (-(25 / 2) - 2 * δ)
  gcongr

lemma intOn_psiR (X : ℝ) : IntegrableOn psiR (Ioc 1 X) := by
  have hφ := (intOn_phi (δ := 1 / 16) (by norm_num)).mono_set (Ioc_subset_Ioi_self : Ioc (1:ℝ) X ⊆ Ioi 1)
  refine (hφ.const_mul (max X 1 ^ (2 * (1 / 16 : ℝ)))).mono'
    measurable_psiR.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hx0 : 0 < x := by linarith [hx.1]
  rw [Real.norm_of_nonneg (psiR_nonneg hx0.le), psiR]
  have h := rpow_shift_le hx0 (hx.2.trans (le_max_left X 1)) (by norm_num : (0 : ℝ) ≤ 1 / 16)
  have hS : 0 ≤ S x ^ 2 := sq_nonneg _
  calc S x ^ 2 * x ^ (-(25 / 2 : ℝ))
      ≤ S x ^ 2 * (max X 1 ^ (2 * (1 / 16 : ℝ)) * x ^ (-(25 / 2) - 2 * (1 / 16 : ℝ))) := by gcongr
    _ = _ := by ring

/-- **Upper log mean square**: `∫₁^X S² x^{−25/2} ≤ e² C log X` for `X ≥ e^{16}`. -/
theorem log_mean_upper : ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, Real.exp 16 ≤ X →
    ∫ x in Ioc 1 X, psiR x ≤ C * Real.log X := by
  obtain ⟨c, C, hc, hC, hb⟩ := tau_mean_square_mellin
  refine ⟨Real.exp 2 * C, by positivity, fun X hX => ?_⟩
  have hX1 : 1 < X := by have := Real.add_one_le_exp (16 : ℝ); linarith
  have hX0 : 0 < X := by linarith
  have hL : 16 ≤ Real.log X := by
    rw [← Real.log_exp 16]; exact Real.log_le_log (Real.exp_pos _) hX
  set δ : ℝ := 1 / Real.log X with hδ
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδ1 : δ ≤ 1 / 16 := by rw [hδ]; exact one_div_le_one_div_of_le (by norm_num) hL
  have hXδ : X ^ (2 * δ) = Real.exp 2 := by
    rw [Real.rpow_def_of_pos hX0, hδ]; congr 1; field_simp
  have hφ := intOn_phi hδ0
  have hpt : ∀ x ∈ Ioc 1 X, psiR x ≤ Real.exp 2 * (S x ^ 2 * x ^ (-(25 / 2) - 2 * δ)) := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have h := rpow_shift_le hx0 hx.2 hδ0.le
    rw [hXδ] at h
    rw [psiR]
    have hS : 0 ≤ S x ^ 2 := sq_nonneg _
    calc S x ^ 2 * x ^ (-(25 / 2 : ℝ)) ≤ S x ^ 2 * (Real.exp 2 * x ^ (-(25 / 2) - 2 * δ)) := by
          gcongr
      _ = _ := by ring
  have h1 : ∫ x in Ioc 1 X, psiR x ≤
      ∫ x in Ioc 1 X, Real.exp 2 * (S x ^ 2 * x ^ (-(25 / 2) - 2 * δ)) :=
    setIntegral_mono_on (intOn_psiR X) ((hφ.mono_set Ioc_subset_Ioi_self).const_mul _)
      measurableSet_Ioc hpt
  have h2 : ∫ x in Ioc 1 X, S x ^ 2 * x ^ (-(25 / 2) - 2 * δ) ≤
      ∫ x in Ioi (1 : ℝ), S x ^ 2 * x ^ (-(25 / 2) - 2 * δ) := by
    refine setIntegral_mono_set hφ ?_ Ioc_subset_Ioi_self.eventuallyLE
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) ≤ x := le_of_lt (lt_trans zero_lt_one hx)
    have := Real.rpow_nonneg hx0 (-(25 / 2) - 2 * δ)
    positivity
  rw [integral_const_mul] at h1
  have h3 := (hb δ hδ0 hδ1).2
  have hδinv : C / δ = C * Real.log X := by rw [hδ]; field_simp
  calc ∫ x in Ioc 1 X, psiR x ≤ Real.exp 2 * ∫ x in Ioc 1 X, S x ^ 2 * x ^ (-(25 / 2) - 2 * δ) := h1
    _ ≤ Real.exp 2 * (C / δ) := by gcongr; exact h2.trans h3
    _ = Real.exp 2 * C * Real.log X := by rw [hδinv]; ring

/-- **Lower log mean square**: `∫₁^X S² x^{−25/2} ≥ c log X` for `X ≥ X₀`. -/
theorem log_mean_lower : ∃ c X0 : ℝ, 0 < c ∧ 1 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X →
    c * Real.log X ≤ ∫ x in Ioc 1 X, psiR x := by
  obtain ⟨c, C, hc, hC, hb⟩ := tau_mean_square_mellin
  set L : ℝ := 4 * C / c + 1 with hLdef
  have hL0 : 0 < L := by rw [hLdef]; positivity
  refine ⟨c / (2 * L), Real.exp (16 * L), by positivity,
    by have := Real.add_one_le_exp (16 * L); linarith, fun X hX => ?_⟩
  have hX1 : 1 < X := by have := Real.add_one_le_exp (16 * L); linarith
  have hX0 : 0 < X := by linarith
  have hlog : 16 * L ≤ Real.log X := by
    rw [← Real.log_exp (16 * L)]; exact Real.log_le_log (Real.exp_pos _) hX
  have hlogpos : 0 < Real.log X := by linarith
  set δ : ℝ := L / Real.log X with hδ
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδ1 : δ ≤ 1 / 16 := by
    rw [hδ, div_le_iff₀ hlogpos]; linarith
  have hXδ : X ^ (-δ) = Real.exp (-L) := by
    rw [Real.rpow_def_of_pos hX0, hδ]; congr 1; field_simp
  have heL : Real.exp (-L) ≤ c / (4 * C) := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity)]
    have := Real.add_one_le_exp L
    rw [inv_div]
    have : 4 * C / c < L + 1 := by rw [hLdef]; linarith
    linarith
  set φ : ℝ → ℝ := fun x => S x ^ 2 * x ^ (-(25 / 2) - 2 * δ) with hφdef
  set φ2 : ℝ → ℝ := fun x => S x ^ 2 * x ^ (-(25 / 2) - 2 * (δ / 2)) with hφ2def
  have hφi : IntegrableOn φ (Ioi 1) := intOn_phi hδ0
  have hφ2i : IntegrableOn φ2 (Ioi 1) := intOn_phi (by linarith)
  -- split `(1,∞) = (1,X] ∪ (X,∞)`
  have hsplit : ∫ x in Ioi (1 : ℝ), φ x = (∫ x in Ioc 1 X, φ x) + ∫ x in Ioi X, φ x := by
    rw [← Ioc_union_Ioi_eq_Ioi hX1.le, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hφi.mono_set Ioc_subset_Ioi_self) (hφi.mono_set (Ioi_subset_Ioi hX1.le))]
  -- near part
  have hnear : ∫ x in Ioc 1 X, φ x ≤ ∫ x in Ioc 1 X, psiR x := by
    refine setIntegral_mono_on (hφi.mono_set Ioc_subset_Ioi_self) (intOn_psiR X) measurableSet_Ioc
      fun x hx => ?_
    have hx1 : 1 ≤ x := hx.1.le
    simp only [hφdef, psiR]
    have : x ^ (-(25 / 2) - 2 * δ) ≤ x ^ (-(25 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have hS : 0 ≤ S x ^ 2 := sq_nonneg _
    gcongr
  -- far part
  have hfar : ∫ x in Ioi X, φ x ≤ X ^ (-δ) * ∫ x in Ioi (1 : ℝ), φ2 x := by
    have h1 : ∫ x in Ioi X, φ x ≤ ∫ x in Ioi X, X ^ (-δ) * φ2 x := by
      refine setIntegral_mono_on (hφi.mono_set (Ioi_subset_Ioi hX1.le))
        ((hφ2i.mono_set (Ioi_subset_Ioi hX1.le)).const_mul _) measurableSet_Ioi fun x hx => ?_
      have hx0 : 0 < x := lt_trans hX0 hx
      simp only [hφdef, hφ2def]
      have e : x ^ (-(25 / 2) - 2 * δ) = x ^ (-δ) * x ^ (-(25 / 2) - 2 * (δ / 2)) := by
        rw [← Real.rpow_add hx0]; congr 1; ring
      have h2 : x ^ (-δ) ≤ X ^ (-δ) :=
        Real.rpow_le_rpow_of_nonpos hX0 (le_of_lt hx) (by linarith)
      rw [e]
      have := Real.rpow_nonneg hx0.le (-(25 / 2) - 2 * (δ / 2))
      have hS : 0 ≤ S x ^ 2 := sq_nonneg _
      calc S x ^ 2 * (x ^ (-δ) * x ^ (-(25 / 2) - 2 * (δ / 2)))
          ≤ S x ^ 2 * (X ^ (-δ) * x ^ (-(25 / 2) - 2 * (δ / 2))) := by gcongr
        _ = _ := by ring
    rw [integral_const_mul] at h1
    refine h1.trans ?_
    have hXp : 0 < X ^ (-δ) := Real.rpow_pos_of_pos hX0 _
    refine mul_le_mul_of_nonneg_left ?_ hXp.le
    refine setIntegral_mono_set hφ2i ?_ (Ioi_subset_Ioi hX1.le).eventuallyLE
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) ≤ x := le_of_lt (lt_trans zero_lt_one hx)
    have := Real.rpow_nonneg hx0 (-(25 / 2) - 2 * (δ / 2))
    simp only [hφ2def]; positivity
  have hlow := (hb δ hδ0 hδ1).1
  have hup2 := (hb (δ / 2) (by linarith) (by linarith)).2
  have hfar' : ∫ x in Ioi X, φ x ≤ c / (2 * δ) := by
    refine hfar.trans ?_
    rw [hXδ]
    calc Real.exp (-L) * ∫ x in Ioi (1 : ℝ), φ2 x ≤ c / (4 * C) * (C / (δ / 2)) := by
          gcongr
          · exact setIntegral_nonneg measurableSet_Ioi fun x hx => by
              have hx0 : (0 : ℝ) ≤ x := le_of_lt (lt_trans zero_lt_one hx)
              have := Real.rpow_nonneg hx0 (-(25 / 2) - 2 * (δ / 2))
              simp only [hφ2def]; positivity
      _ = c / (2 * δ) := by field_simp; ring
  have hmain : c / (2 * δ) ≤ ∫ x in Ioc 1 X, psiR x := by
    have : c / δ ≤ (∫ x in Ioc 1 X, φ x) + ∫ x in Ioi X, φ x := by
      rw [← hsplit]; exact hlow
    have e : c / δ = c / (2 * δ) + c / (2 * δ) := by field_simp; ring
    linarith
  have e2 : c / (2 * L) * Real.log X = c / (2 * δ) := by
    rw [hδ]; field_simp
  rw [e2]; exact hmain

/-- **Upper mean square**: `∫₁^X S(x)² dx ≤ C X^{25/2} log X` for `X ≥ e^{16}`. -/
theorem mean_square_upper : ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, Real.exp 16 ≤ X →
    ∫ x in Ioc 1 X, S x ^ 2 ≤ C * X ^ (25 / 2 : ℝ) * Real.log X := by
  obtain ⟨C, hC, h⟩ := log_mean_upper
  refine ⟨C, hC, fun X hX => ?_⟩
  have hX1 : 1 < X := by have := Real.add_one_le_exp (16 : ℝ); linarith
  have hX0 : 0 < X := by linarith
  have hpt : ∀ x ∈ Ioc 1 X, S x ^ 2 ≤ X ^ (25 / 2 : ℝ) * psiR x := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    rw [psiR]
    have e : S x ^ 2 = S x ^ 2 * x ^ (-(25 / 2 : ℝ)) * x ^ (25 / 2 : ℝ) := by
      rw [mul_assoc, ← Real.rpow_add hx0]; norm_num
    have h2 : x ^ (25 / 2 : ℝ) ≤ X ^ (25 / 2 : ℝ) :=
      Real.rpow_le_rpow hx0.le hx.2 (by norm_num)
    have := Real.rpow_nonneg hx0.le (-(25 / 2 : ℝ))
    have hS : 0 ≤ S x ^ 2 := sq_nonneg _
    calc S x ^ 2 = S x ^ 2 * x ^ (-(25 / 2 : ℝ)) * x ^ (25 / 2 : ℝ) := e
      _ ≤ S x ^ 2 * x ^ (-(25 / 2 : ℝ)) * X ^ (25 / 2 : ℝ) := by gcongr
      _ = _ := by ring
  have hint : IntegrableOn (fun x => S x ^ 2) (Ioc 1 X) := by
    refine ((intOn_psiR X).const_mul (X ^ (25 / 2 : ℝ))).mono'
      (measurable_S.pow_const 2).aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hpt x hx
  calc ∫ x in Ioc 1 X, S x ^ 2 ≤ ∫ x in Ioc 1 X, X ^ (25 / 2 : ℝ) * psiR x :=
        setIntegral_mono_on hint ((intOn_psiR X).const_mul _) measurableSet_Ioc hpt
    _ = X ^ (25 / 2 : ℝ) * ∫ x in Ioc 1 X, psiR x := integral_const_mul _ _
    _ ≤ X ^ (25 / 2 : ℝ) * (C * Real.log X) := by gcongr; exact h X hX
    _ = C * X ^ (25 / 2 : ℝ) * Real.log X := by ring

lemma intOn_S2 (X : ℝ) : IntegrableOn (fun x => S x ^ 2) (Ioc 1 X) := by
  refine ((intOn_psiR X).const_mul (max X 1 ^ (25 / 2 : ℝ))).mono'
    (measurable_S.pow_const 2).aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hx0 : 0 < x := by linarith [hx.1]
  rw [Real.norm_of_nonneg (sq_nonneg _), psiR]
  have e : S x ^ 2 = S x ^ 2 * x ^ (-(25 / 2 : ℝ)) * x ^ (25 / 2 : ℝ) := by
    rw [mul_assoc, ← Real.rpow_add hx0]; norm_num
  have h2 : x ^ (25 / 2 : ℝ) ≤ max X 1 ^ (25 / 2 : ℝ) :=
    Real.rpow_le_rpow hx0.le (hx.2.trans (le_max_left _ _)) (by norm_num)
  have := Real.rpow_nonneg hx0.le (-(25 / 2 : ℝ))
  have hS : 0 ≤ S x ^ 2 := sq_nonneg _
  calc S x ^ 2 = S x ^ 2 * x ^ (-(25 / 2 : ℝ)) * x ^ (25 / 2 : ℝ) := e
    _ ≤ S x ^ 2 * x ^ (-(25 / 2 : ℝ)) * max X 1 ^ (25 / 2 : ℝ) := by gcongr
    _ = _ := by ring

lemma iI_psiR {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) : IntervalIntegrable psiR volume a b :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
    ((intOn_psiR b).mono_set (Ioc_subset_Ioc_left ha))

/-- **Ω for the mean square**: `∫₁^X S(x)² dx ≥ c X^{25/2}` for arbitrarily large `X`. -/
theorem mean_square_omega : ∃ c : ℝ, 0 < c ∧ ∀ Y : ℝ, ∃ X : ℝ, Y ≤ X ∧
    c * X ^ (25 / 2 : ℝ) ≤ ∫ x in Ioc 1 X, S x ^ 2 := by
  obtain ⟨cl, X0, hcl, hX01, hlow⟩ := log_mean_lower
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2p : (0 : ℝ) < 2 ^ (25 / 2 : ℝ) := by positivity
  set c : ℝ := cl * Real.log 2 / (2 * 2 ^ (25 / 2 : ℝ)) with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  refine ⟨c, hc0, fun Y => ?_⟩
  by_contra hcon
  push Not at hcon
  set Y1 : ℝ := max Y 1 with hY1
  have hY11 : 1 ≤ Y1 := le_max_right _ _
  have hbound : ∀ X, Y1 ≤ X → ∫ x in Ioc 1 X, S x ^ 2 < c * X ^ (25 / 2 : ℝ) :=
    fun X hX => hcon X (le_trans (le_max_left _ _) hX)
  set b : ℕ → ℝ := fun j => Y1 * 2 ^ j with hb
  have hb1 : ∀ j, Y1 ≤ b j := fun j => by
    simp only [hb]; exact le_mul_of_one_le_right (by linarith) (one_le_pow₀ (by norm_num))
  have hbs : ∀ j, b (j + 1) = 2 * b j := fun j => by simp only [hb]; rw [pow_succ]; ring
  -- each dyadic block contributes at most `c 2^{25/2}`
  have hblock : ∀ j, ∫ x in b j..b (j + 1), psiR x ≤ c * 2 ^ (25 / 2 : ℝ) := by
    intro j
    have hbj0 : 0 < b j := by linarith [hb1 j]
    have hle : b j ≤ b (j + 1) := by rw [hbs]; linarith
    rw [intervalIntegral.integral_of_le hle]
    have hpt : ∀ x ∈ Ioc (b j) (b (j + 1)), psiR x ≤ b j ^ (-(25 / 2 : ℝ)) * S x ^ 2 := by
      intro x hx
      have hx0 : 0 < x := lt_trans hbj0 hx.1
      rw [psiR, mul_comm]
      have := Real.rpow_le_rpow_of_nonpos hbj0 hx.1.le (by norm_num : (-(25 / 2 : ℝ)) ≤ 0)
      have hS : 0 ≤ S x ^ 2 := sq_nonneg _
      gcongr
    have hsub : Ioc (b j) (b (j + 1)) ⊆ Ioc 1 (b (j + 1)) :=
      Ioc_subset_Ioc_left (by linarith [hb1 j])
    have h1 : ∫ x in Ioc (b j) (b (j + 1)), psiR x ≤
        ∫ x in Ioc (b j) (b (j + 1)), b j ^ (-(25 / 2 : ℝ)) * S x ^ 2 :=
      setIntegral_mono_on ((intOn_psiR _).mono_set hsub) (((intOn_S2 _).mono_set hsub).const_mul _)
        measurableSet_Ioc hpt
    rw [integral_const_mul] at h1
    have h2 : ∫ x in Ioc (b j) (b (j + 1)), S x ^ 2 ≤ ∫ x in Ioc 1 (b (j + 1)), S x ^ 2 :=
      setIntegral_mono_set (intOn_S2 _) (Eventually.of_forall fun _ => sq_nonneg _)
        hsub.eventuallyLE
    have h3 := hbound (b (j + 1)) (le_trans (hb1 j) hle)
    have hbp : 0 < b j ^ (-(25 / 2 : ℝ)) := Real.rpow_pos_of_pos hbj0 _
    have e : b j ^ (-(25 / 2 : ℝ)) * (c * b (j + 1) ^ (25 / 2 : ℝ)) = c * 2 ^ (25 / 2 : ℝ) := by
      rw [hbs, Real.mul_rpow (by norm_num) hbj0.le]
      have : b j ^ (-(25 / 2 : ℝ)) * b j ^ (25 / 2 : ℝ) = 1 := by
        rw [← Real.rpow_add hbj0]; norm_num
      calc b j ^ (-(25 / 2 : ℝ)) * (c * (2 ^ (25 / 2 : ℝ) * b j ^ (25 / 2 : ℝ)))
          = c * 2 ^ (25 / 2 : ℝ) * (b j ^ (-(25 / 2 : ℝ)) * b j ^ (25 / 2 : ℝ)) := by ring
        _ = _ := by rw [this, mul_one]
    calc ∫ x in Ioc (b j) (b (j + 1)), psiR x
        ≤ b j ^ (-(25 / 2 : ℝ)) * ∫ x in Ioc (b j) (b (j + 1)), S x ^ 2 := h1
      _ ≤ b j ^ (-(25 / 2 : ℝ)) * (c * b (j + 1) ^ (25 / 2 : ℝ)) := by
          gcongr; exact h2.trans h3.le
      _ = _ := e
  set D : ℝ := ∫ x in (1 : ℝ)..Y1, psiR x with hD
  have hsum : ∀ n : ℕ, ∫ x in (1 : ℝ)..b n, psiR x ≤ D + n * (c * 2 ^ (25 / 2 : ℝ)) := by
    intro n
    have hadj : ∑ j ∈ Finset.range n, ∫ x in b j..b (j + 1), psiR x = ∫ x in b 0..b n, psiR x :=
      intervalIntegral.sum_integral_adjacent_intervals fun j _ =>
        iI_psiR (le_trans hY11 (hb1 j)) (by rw [hbs]; linarith [hb1 j])
    have hb0 : b 0 = Y1 := by simp [hb]
    rw [hb0] at hadj
    rw [← intervalIntegral.integral_add_adjacent_intervals (iI_psiR le_rfl hY11)
      (iI_psiR hY11 (hb1 n)), ← hadj]
    have := Finset.sum_le_sum fun j (_ : j ∈ Finset.range n) => hblock j
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    linarith
  -- choose `n` large
  obtain ⟨n, hn⟩ := exists_nat_gt (max X0 (2 * D / (cl * Real.log 2)))
  have hnX0 : X0 < n := lt_of_le_of_lt (le_max_left _ _) hn
  have hnD : 2 * D / (cl * Real.log 2) < n := lt_of_le_of_lt (le_max_right _ _) hn
  have h2n : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self).le
  have hbn : X0 ≤ b n := by
    simp only [hb]
    have : (2 : ℝ) ^ n ≤ Y1 * 2 ^ n := le_mul_of_one_le_left (by positivity) hY11
    linarith
  have hlb := hlow (b n) hbn
  have hlogb : n * Real.log 2 ≤ Real.log (b n) := by
    simp only [hb]
    rw [Real.log_mul (by linarith) (by positivity), Real.log_pow]
    have := Real.log_nonneg hY11
    linarith
  have hint : ∫ x in Ioc 1 (b n), psiR x = ∫ x in (1 : ℝ)..b n, psiR x :=
    (intervalIntegral.integral_of_le (le_trans hY11 (hb1 n))).symm
  rw [hint] at hlb
  have hs := hsum n
  have hcl2 : cl * (n * Real.log 2) ≤ cl * Real.log (b n) := by gcongr
  have hce : (n : ℝ) * (c * 2 ^ (25 / 2 : ℝ)) = cl * (n * Real.log 2) / 2 := by
    rw [hc]; field_simp
  have hfin : cl * (n * Real.log 2) / 2 ≤ D := by linarith
  have : 2 * D < n * (cl * Real.log 2) := by
    rw [div_lt_iff₀ (by positivity)] at hnD; linarith
  nlinarith

/-! ### Unconditional Mellin identity for `S` on `Re w > 23/4` -/

lemma A_Dl_eq (x : ℝ) : A Dl x = ((S x : ℝ) : ℂ) := by
  rw [A, S]; simp_rw [coef_discriminant]; push_cast; rfl

/-- `∫₁^∞ S(x) x^{−w−1} dx` converges absolutely for `Re w > 23/4`. -/
theorem mc_A {s : ℂ} (hs : 23 / 4 < s.re) : MellinConvergent (A Dl) (-s) := by
  set σ : ℝ := s.re with hσ
  set σ' : ℝ := (σ + 23 / 4) / 2 with hσ'
  have hg := mc_all (2 * σ') (by rw [hσ']; linarith)
  unfold MellinConvergent at hg ⊢
  set p : ℝ := 2 * σ' - 2 * σ - 1 with hp
  have hp1 : p < -1 := by rw [hp, hσ']; linarith
  have hI : Integrable ((Ici (1 : ℝ)).indicator fun t : ℝ => t ^ p) :=
    (integrable_indicator_iff measurableSet_Ici).2
      ((integrableOn_Ici_iff_integrableOn_Ioi).2 (integrableOn_Ioi_rpow_of_lt hp1 zero_lt_one))
  refine ((hg.norm.add hI.integrableOn).div_const 2).mono'
    (RamanujanTau.TauOmegaPM.aesm_integrand (measurable_A Dl) (-s) _) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0 : ℝ) < t := ht
  simp only [Pi.add_apply]
  rw [RamanujanTau.TauOmegaPM.norm_integrand ht0, RamanujanTau.TauOmegaPM.norm_integrand ht0]
  simp only [Complex.neg_re, Complex.ofReal_re]
  rcases lt_or_ge t 1 with h1 | h1
  · rw [A_of_lt_one Dl h1, norm_zero, mul_zero]
    have : 0 ≤ (Ici (1 : ℝ)).indicator (fun t : ℝ => t ^ p) t :=
      Set.indicator_nonneg (fun _ _ => Real.rpow_nonneg ht0.le _) _
    have : 0 ≤ t ^ (-(2 * σ') - 1) * ‖gC t‖ := by positivity
    linarith
  · rw [Set.indicator_of_mem (show t ∈ Ici (1 : ℝ) from h1), gC, Complex.norm_real,
      Real.norm_of_nonneg (gsq_nonneg t), gsq]
    set a : ℝ := t ^ (-σ' - 1 / 2) * ‖A Dl t‖ with ha
    set b : ℝ := t ^ (σ' - σ - 1 / 2) with hb
    have e1 : t ^ (-σ - 1) * ‖A Dl t‖ = a * b := by
      rw [ha, hb, mul_comm (t ^ (-σ' - 1 / 2)), mul_assoc, ← Real.rpow_add ht0]
      ring_nf
    have e2 : t ^ (-(2 * σ') - 1) * ‖A Dl t‖ ^ 2 = a ^ 2 := by
      rw [ha, mul_pow, ← Real.rpow_natCast (t ^ (-σ' - 1 / 2)) 2, ← Real.rpow_mul ht0.le]; ring_nf
    have e3 : t ^ p = b ^ 2 := by
      rw [hb, ← Real.rpow_natCast (t ^ (σ' - σ - 1 / 2)) 2, ← Real.rpow_mul ht0.le, hp]; ring_nf
    rw [e1, e2, e3]
    nlinarith [sq_nonneg (a - b)]

/-- **Unconditional Mellin identity**: `∫₁^∞ S(x) x^{−w−1} dx = L(Δ,w)/w` for `Re w > 23/4`. -/
theorem tau_mellin_uncond {w : ℂ} (hw : 23 / 4 < w.re) :
    MellinConvergent (A Dl) (-w) ∧ mellin (A Dl) (-w) = tauL w / w := by
  refine ⟨mc_A hw, ?_⟩
  have h := RamanujanTau.TauOmegaPM.mellin_A_eq_of_conv Dl (by norm_num) (β := 23 / 4)
    (by norm_num) (fun s hs => mc_A hs) w hw
  rw [h, fL_Dl]

end RamanujanTau.Voronoi
