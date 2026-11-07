/-
# M2.2: one off-diagonal `t`-integral, by two integrations by parts

For `T ≥ 1`, `0 ≤ x ≤ 1`, `|v| ≤ 1`, `ξ > 0`, `ω ≠ 0`, with the window `φ_T` (`Window.lean`):

    J = ∫_{T/2}^{3T} φ_T(t) U(t+x, t+x+v) W̃_{t+x,t+x+v}(ξ) e^{iωt} dt,
    |J| ≤ C ω^{−2} T^{−1} (1 + ξ/T²)^{−A}         (`farTerm_bound`)
    |J| ≤ C T (1 + ξ/T²)^{−A}                     (`farTerm_trivial`).

Inputs: `SelbergKey3.ibp_twice`, M2.0 (`Phase.Ulag_bounds`), M2.1 (`Window`),
`SelbergKey3.Wlag_iteratedDeriv_bound` (`j = 1, 2`), `SelbergKey2.Wsh_bound`.
Level 1.
-/
import RamanujanTau.SelbergKey4.Phase
import RamanujanTau.SelbergKey4.Window

set_option autoImplicit false

namespace RamanujanTau.SelbergKey4

open Complex MeasureTheory Set Filter Topology RamanujanTau.HeckeAFE RamanujanTau.HeckeAFE2
  RamanujanTau.HeckeAFE3 RamanujanTau.SelbergKey RamanujanTau.SelbergKey2 RamanujanTau.SelbergKey3
open scoped Real

/-! ## A `C²` package and its product rule -/

/-- `f` is `C²` with `f' = f1`, `f'' = f2` everywhere. -/
structure C2 (f f1 f2 : ℝ → ℂ) : Prop where
  d0 : ∀ t, HasDerivAt f (f1 t) t
  d1 : ∀ t, HasDerivAt f1 (f2 t) t
  c2 : Continuous f2

lemma C2.cont0 {f f1 f2 : ℝ → ℂ} (h : C2 f f1 f2) : Continuous f :=
  continuous_iff_continuousAt.2 fun t => (h.d0 t).continuousAt

lemma C2.cont1 {f f1 f2 : ℝ → ℂ} (h : C2 f f1 f2) : Continuous f1 :=
  continuous_iff_continuousAt.2 fun t => (h.d1 t).continuousAt

lemma C2.mul {f f1 f2 g g1 g2 : ℝ → ℂ} (hf : C2 f f1 f2) (hg : C2 g g1 g2) :
    C2 (fun t => f t * g t) (fun t => f1 t * g t + f t * g1 t)
      (fun t => f2 t * g t + 2 * (f1 t * g1 t) + f t * g2 t) where
  d0 t := (hf.d0 t).mul (hg.d0 t)
  d1 t := by
    have h := ((hf.d1 t).mul (hg.d0 t)).add ((hf.d0 t).mul (hg.d1 t))
    convert h using 1; ring
  c2 := by
    have := hf.c2; have := hg.c2; have := hf.cont0; have := hf.cont1; have := hg.cont0
    have := hg.cont1
    fun_prop

lemma C2.comp_add {f f1 f2 : ℝ → ℂ} (h : C2 f f1 f2) (x : ℝ) :
    C2 (fun t => f (t + x)) (fun t => f1 (t + x)) (fun t => f2 (t + x)) where
  d0 t := (h.d0 (t + x)).comp_add_const t x
  d1 t := (h.d1 (t + x)).comp_add_const t x
  c2 := h.c2.comp (continuous_id.add continuous_const)

/-! ## The three factors -/

lemma C2_phiT (T : ℝ) :
    C2 (fun t => ((phiT T t : ℝ) : ℂ)) (fun t => ((Phi1 (t / T) / T : ℝ) : ℂ))
      (fun t => ((Phi2 (t / T) / T ^ 2 : ℝ) : ℂ)) where
  d0 t := (hasDerivAt_phiT t).ofReal_comp
  d1 t := (hasDerivAt_phiT1 t).ofReal_comp
  c2 := Complex.continuous_ofReal.comp
    ((continuous_Phi2.comp (continuous_id.div_const T)).div_const _)

lemma C2_Ulag (v : ℝ) :
    C2 (Ulag v) (fun u => I * (dlt v u : ℂ) * Ulag v u)
      (fun u => (I * (dlt1 v u : ℂ) - (dlt v u : ℂ) ^ 2) * Ulag v u) where
  d0 := hasDerivAt_Ulag v
  d1 := hasDerivAt_Ulag1 v
  c2 := continuous_Ulag2 v

/-- `W(u) = W̃_{u,u+v}(ξ)` as a function of `u`. -/
noncomputable def Wv (v ξ u : ℝ) : ℂ := Wsh u (u + v) ξ

lemma hasDerivAt_Wv0 {v ξ : ℝ} (hv : |v| ≤ 1) (hξ : 0 < ξ) (u : ℝ) :
    HasDerivAt (Wv v ξ) (iteratedDeriv 1 (Wv v ξ) u) u := by
  have e : Wv v ξ = Wl 1 v ξ := by funext w; exact Wsh_eq_Wl_pos one_pos hξ w v
  rw [e, iteratedDeriv_Wl (by norm_num) one_ne_zero hξ hv 1]
  have h := hasDerivAt_intPd (x := 1) (by norm_num) one_ne_zero hξ 0 hv u
  have e2 : (fun u => ∫ y : ℝ, Pd 1 v 0 u y * Kf 1 ξ y) = Wl 1 v ξ := by
    funext w; unfold Wl; congr 1; funext y; rw [Pd_zero]
  rw [e2] at h
  exact h

theorem Wv_package (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v ξ : ℝ, |v| ≤ 1 → 0 < ξ →
      C2 (Wv v ξ) (iteratedDeriv 1 (Wv v ξ)) (iteratedDeriv 2 (Wv v ξ)) ∧
      ∀ u : ℝ, ‖Wv v ξ u‖ ≤ C * (1 + ξ / (Tq u * Tq (u + v))) ^ (-A) ∧
        ‖iteratedDeriv 1 (Wv v ξ) u‖ ≤ C / (1 + |u|) * (1 + ξ / (Tq u * Tq (u + v))) ^ (-A) ∧
        ‖iteratedDeriv 2 (Wv v ξ) u‖ ≤ C / (1 + |u|) ^ 2 * (1 + ξ / (Tq u * Tq (u + v))) ^ (-A) := by
  obtain ⟨C0, hC00, hC0⟩ := Wsh_bound hA
  obtain ⟨C1, hC10, hC1⟩ := Wlag_iteratedDeriv_bound (j := 1) le_rfl hA
  obtain ⟨C2', hC20, hC2⟩ := Wlag_iteratedDeriv_bound (j := 2) (by norm_num) hA
  refine ⟨C0 + C1 + C2', by positivity, fun v ξ hv hξ => ⟨⟨hasDerivAt_Wv0 hv hξ,
    fun t => (hC1 t v ξ hv hξ).1, ?_⟩, fun u => ⟨?_, ?_, ?_⟩⟩⟩
  · exact continuous_iff_continuousAt.2 fun t => (hC2 t v ξ hv hξ).1.continuousAt
  · have hR : 0 ≤ (1 + ξ / (Tq u * Tq (u + v))) ^ (-A) := Real.rpow_nonneg (by
      have := Tq_pos u; have := Tq_pos (u + v); positivity) _
    refine (hC0 u (u + v) ξ hξ).trans ?_
    gcongr; linarith
  · have hR : 0 ≤ (1 + ξ / (Tq u * Tq (u + v))) ^ (-A) := Real.rpow_nonneg (by
      have := Tq_pos u; have := Tq_pos (u + v); positivity) _
    refine (hC1 u v ξ hv hξ).2.trans ?_
    rw [pow_one]
    gcongr; linarith
  · have hR : 0 ≤ (1 + ξ / (Tq u * Tq (u + v))) ^ (-A) := Real.rpow_nonneg (by
      have := Tq_pos u; have := Tq_pos (u + v); positivity) _
    refine (hC2 u v ξ hv hξ).2.trans ?_
    gcongr; linarith

/-! ## The amplitude `F = U·W` -/

/-- `F(u) = U(u,u+v) W̃_{u,u+v}(ξ)`. -/
noncomputable def FW (v ξ u : ℝ) : ℂ := Ulag v u * Wv v ξ u

noncomputable def FW1 (v ξ u : ℝ) : ℂ :=
  I * (dlt v u : ℂ) * Ulag v u * Wv v ξ u + Ulag v u * iteratedDeriv 1 (Wv v ξ) u

noncomputable def FW2 (v ξ u : ℝ) : ℂ :=
  (I * (dlt1 v u : ℂ) - (dlt v u : ℂ) ^ 2) * Ulag v u * Wv v ξ u +
    2 * (I * (dlt v u : ℂ) * Ulag v u * iteratedDeriv 1 (Wv v ξ) u) +
    Ulag v u * iteratedDeriv 2 (Wv v ξ) u

theorem FW_package (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v ξ : ℝ, |v| ≤ 1 → 0 < ξ →
      C2 (FW v ξ) (FW1 v ξ) (FW2 v ξ) ∧
      ∀ u : ℝ, ‖FW v ξ u‖ ≤ C * (1 + ξ / (Tq u * Tq (u + v))) ^ (-A) ∧
        ‖FW1 v ξ u‖ ≤ C / (1 + |u|) * (1 + ξ / (Tq u * Tq (u + v))) ^ (-A) ∧
        ‖FW2 v ξ u‖ ≤ C / (1 + |u|) ^ 2 * (1 + ξ / (Tq u * Tq (u + v))) ^ (-A) := by
  obtain ⟨CW, hCW0, hCW⟩ := Wv_package A hA
  obtain ⟨CU, hCU0, hCU⟩ := Ulag_bounds
  refine ⟨(1 + CU) * CW * 4, by positivity, fun v ξ hv hξ => ⟨?_, fun u => ?_⟩⟩
  · have h := (C2_Ulag v).mul (hCW v ξ hv hξ).1
    convert h using 1
  obtain ⟨hU0, hU1, hU2⟩ := hCU u v hv
  obtain ⟨hW0, hW1, hW2⟩ := (hCW v ξ hv hξ).2 u
  set R := (1 + ξ / (Tq u * Tq (u + v))) ^ (-A)
  have hR : 0 ≤ R := Real.rpow_nonneg (by
      have := Tq_pos u; have := Tq_pos (u + v); positivity) _
  have hu1 : 1 ≤ 1 + |u| := by linarith [abs_nonneg u]
  have hu0 : 0 < 1 + |u| := by linarith
  have hk : (1 + |u|)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hu1
  set a := (1 + |u|)⁻¹ with ha
  have ha0 : 0 ≤ a := by positivity
  have e1 : ∀ c : ℝ, c / (1 + |u|) = c * a := fun c => by rw [ha, div_eq_mul_inv]
  have e2 : ∀ c : ℝ, c / (1 + |u|) ^ 2 = c * a ^ 2 := fun c => by rw [ha, inv_pow, div_eq_mul_inv]
  rw [e1] at hU1 hW1 ⊢
  rw [e2] at hU2 hW2 ⊢
  refine ⟨?_, ?_, ?_⟩
  · unfold FW; rw [norm_mul, hU0, one_mul]
    refine hW0.trans ?_
    have : CW ≤ (1 + CU) * CW * 4 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hR
  · unfold FW1
    refine (norm_add_le _ _).trans ?_
    have e : ‖I * (dlt v u : ℂ) * Ulag v u * Wv v ξ u‖ =
        ‖I * (dlt v u : ℂ) * Ulag v u‖ * ‖Wv v ξ u‖ := norm_mul _ _
    have e' : ‖Ulag v u * iteratedDeriv 1 (Wv v ξ) u‖ = ‖iteratedDeriv 1 (Wv v ξ) u‖ := by
      rw [norm_mul, hU0, one_mul]
    rw [e, e']
    calc ‖I * (dlt v u : ℂ) * Ulag v u‖ * ‖Wv v ξ u‖ + ‖iteratedDeriv 1 (Wv v ξ) u‖
        ≤ CU * a * (CW * R) + CW * a * R := add_le_add
          (mul_le_mul hU1 hW0 (norm_nonneg _) (by positivity)) hW1
      _ ≤ (1 + CU) * CW * 4 * a * R := by
          have p1 := mul_nonneg (mul_nonneg hCU0 hCW0) (mul_nonneg ha0 hR)
          have p2 := mul_nonneg hCW0 (mul_nonneg ha0 hR)
          nlinarith
  · unfold FW2
    refine (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl) |>.trans ?_
    have f1 : ‖(I * (dlt1 v u : ℂ) - (dlt v u : ℂ) ^ 2) * Ulag v u * Wv v ξ u‖ =
        ‖(I * (dlt1 v u : ℂ) - (dlt v u : ℂ) ^ 2) * Ulag v u‖ * ‖Wv v ξ u‖ := norm_mul _ _
    have f2 : ‖2 * (I * (dlt v u : ℂ) * Ulag v u * iteratedDeriv 1 (Wv v ξ) u)‖ =
        2 * (‖I * (dlt v u : ℂ) * Ulag v u‖ * ‖iteratedDeriv 1 (Wv v ξ) u‖) := by
      rw [norm_mul, Complex.norm_ofNat, norm_mul]
    have f3 : ‖Ulag v u * iteratedDeriv 2 (Wv v ξ) u‖ = ‖iteratedDeriv 2 (Wv v ξ) u‖ := by
      rw [norm_mul, hU0, one_mul]
    rw [f1, f2, f3]
    have t1 := mul_le_mul hU2 hW0 (norm_nonneg _) (by positivity)
    have t2 := mul_le_mul hU1 hW1 (norm_nonneg _) (by positivity)
    have ha2 : a ^ 2 ≤ a := by nlinarith
    calc ‖(I * (dlt1 v u : ℂ) - (dlt v u : ℂ) ^ 2) * Ulag v u‖ * ‖Wv v ξ u‖ +
          2 * (‖I * (dlt v u : ℂ) * Ulag v u‖ * ‖iteratedDeriv 1 (Wv v ξ) u‖) +
          ‖iteratedDeriv 2 (Wv v ξ) u‖
        ≤ CU * a ^ 2 * (CW * R) + 2 * (CU * a * (CW * a * R)) + CW * a ^ 2 * R := by
          gcongr
      _ = (3 * CU * CW + CW) * a ^ 2 * R := by ring
      _ ≤ (1 + CU) * CW * 4 * a ^ 2 * R := by
          have : 0 ≤ CW * a ^ 2 * R := by positivity
          have : 0 ≤ CU * CW * a ^ 2 * R := by positivity
          nlinarith

/-! ## Localization: `u ≍ T` on the support of the window -/

lemma Tq_le (t : ℝ) : Tq t ≤ 3 / 2 + |t| := by
  unfold Tq
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  norm_num

lemma R_le {A T ξ u v : ℝ} (hA : 0 ≤ A) (hT : 1 ≤ T) (hξ : 0 < ξ) (hu0 : 0 ≤ u)
    (hu : u ≤ 4 * T) (hv : |v| ≤ 1) :
    (1 + ξ / (Tq u * Tq (u + v))) ^ (-A) ≤ 64 ^ A * (1 + ξ / T ^ 2) ^ (-A) := by
  have h1 : Tq u ≤ 8 * T := by
    have := Tq_le u; rw [abs_of_nonneg hu0] at this; linarith
  have h2 : Tq (u + v) ≤ 8 * T := by
    have := Tq_le (u + v)
    have : |u + v| ≤ |u| + |v| := abs_add_le u v
    rw [abs_of_nonneg hu0] at this; linarith
  have hT0 : 0 < T := by linarith
  have hq : Tq u * Tq (u + v) ≤ 64 * T ^ 2 := by
    have := Tq_pos u; have := Tq_pos (u + v)
    calc Tq u * Tq (u + v) ≤ (8 * T) * (8 * T) := mul_le_mul h1 h2 (by linarith) (by linarith)
      _ = 64 * T ^ 2 := by ring
  have hqp : 0 < Tq u * Tq (u + v) := mul_pos (Tq_pos u) (Tq_pos (u + v))
  have hlow : (1 + ξ / T ^ 2) / 64 ≤ 1 + ξ / (Tq u * Tq (u + v)) := by
    have : ξ / (64 * T ^ 2) ≤ ξ / (Tq u * Tq (u + v)) :=
      div_le_div_of_nonneg_left hξ.le hqp hq
    have e : (1 + ξ / T ^ 2) / 64 = 1 / 64 + ξ / (64 * T ^ 2) := by field_simp
    rw [e]; linarith
  have hp : 0 < (1 + ξ / T ^ 2) / 64 := by positivity
  calc (1 + ξ / (Tq u * Tq (u + v))) ^ (-A) ≤ ((1 + ξ / T ^ 2) / 64) ^ (-A) :=
        Real.rpow_le_rpow_of_nonpos hp hlow (by linarith)
    _ = 64 ^ A * (1 + ξ / T ^ 2) ^ (-A) := by
        rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 64),
          div_inv_eq_mul, mul_comm]

/-! ## The integrand and its second derivative -/

/-- `g(t) = φ_T(t) F(t+x)`. -/
noncomputable def gT (T x v ξ t : ℝ) : ℂ := ((phiT T t : ℝ) : ℂ) * FW v ξ (t + x)

noncomputable def gT1 (T x v ξ t : ℝ) : ℂ :=
  ((Phi1 (t / T) / T : ℝ) : ℂ) * FW v ξ (t + x) + ((phiT T t : ℝ) : ℂ) * FW1 v ξ (t + x)

noncomputable def gT2 (T x v ξ t : ℝ) : ℂ :=
  ((Phi2 (t / T) / T ^ 2 : ℝ) : ℂ) * FW v ξ (t + x) +
    2 * (((Phi1 (t / T) / T : ℝ) : ℂ) * FW1 v ξ (t + x)) + ((phiT T t : ℝ) : ℂ) * FW2 v ξ (t + x)

lemma C2_gT {T x v ξ : ℝ} (h : C2 (FW v ξ) (FW1 v ξ) (FW2 v ξ)) :
    C2 (gT T x v ξ) (gT1 T x v ξ) (gT2 T x v ξ) :=
  (C2_phiT T).mul (h.comp_add x)

theorem gT2_bound (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T x v ξ : ℝ, 1 ≤ T → 0 ≤ x → x ≤ 1 → |v| ≤ 1 → 0 < ξ →
      C2 (gT T x v ξ) (gT1 T x v ξ) (gT2 T x v ξ) ∧
      ∀ t : ℝ, ‖gT T x v ξ t‖ ≤ C * (1 + ξ / T ^ 2) ^ (-A) ∧
        ‖gT2 T x v ξ t‖ ≤ C / T ^ 2 * (1 + ξ / T ^ 2) ^ (-A) := by
  obtain ⟨CF, hCF0, hCF⟩ := FW_package A hA
  obtain ⟨M, hM0, hM⟩ := Phi_bounds
  refine ⟨64 ^ A * (M * CF) * 16, by positivity, fun T x v ξ hT hx0 hx1 hv hξ =>
    ⟨C2_gT (hCF v ξ hv hξ).1, fun t => ?_⟩⟩
  have hT0 : 0 < T := by linarith
  set S := (1 + ξ / T ^ 2) ^ (-A)
  have hS : 0 ≤ S := Real.rpow_nonneg (by positivity) _
  by_cases ht : t ∈ Icc (3 / 4 * T) (11 / 4 * T)
  · set u := t + x
    have hu0 : 0 ≤ u := by have := ht.1; simp only [u]; nlinarith
    have hu4 : u ≤ 4 * T := by have := ht.2; simp only [u]; linarith
    have hRS := R_le hA hT hξ hu0 hu4 hv
    have hu1 : T / 2 ≤ 1 + |u| := by rw [abs_of_nonneg hu0]; have := ht.1; simp only [u]; nlinarith
    obtain ⟨hF0, hF1, hF2⟩ := (hCF v ξ hv hξ).2 u
    obtain ⟨hP0, hP1, hP2⟩ := hM (t / T)
    set R := (1 + ξ / (Tq u * Tq (u + v))) ^ (-A)
    have hR0 : 0 ≤ R := Real.rpow_nonneg (by
      have := Tq_pos u; have := Tq_pos (u + v); positivity) _
    have hinv1 : 1 / (1 + |u|) ≤ 2 / T := by
      rw [div_le_div_iff₀ (by positivity) hT0]; linarith
    have hinv2 : 1 / (1 + |u|) ^ 2 ≤ 4 / T ^ 2 := by
      have : (1 / (1 + |u|)) ^ 2 ≤ (2 / T) ^ 2 := pow_le_pow_left₀ (by positivity) hinv1 2
      rw [div_pow, div_pow, one_pow] at this; norm_num at this ⊢; linarith
    have hF1' : ‖FW1 v ξ u‖ ≤ CF * (2 / T) * R := by
      refine hF1.trans ?_
      rw [div_eq_mul_one_div CF]; gcongr
    have hF2' : ‖FW2 v ξ u‖ ≤ CF * (4 / T ^ 2) * R := by
      refine hF2.trans ?_
      rw [div_eq_mul_one_div CF]; gcongr
    have hP0' : ‖((phiT T t : ℝ) : ℂ)‖ ≤ M := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hP0
    have hP1' : ‖((Phi1 (t / T) / T : ℝ) : ℂ)‖ ≤ M / T := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hT0]; gcongr
    have hP2' : ‖((Phi2 (t / T) / T ^ 2 : ℝ) : ℂ)‖ ≤ M / T ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0:ℝ) < T ^ 2)]
      gcongr
    have hRS' : R ≤ 64 ^ A * S := hRS
    have h64 : 0 ≤ (64 : ℝ) ^ A := by positivity
    have hT1 : 1 / T ≤ 1 := by rw [div_le_one hT0]; exact hT
    constructor
    · unfold gT
      rw [norm_mul]
      calc ‖((phiT T t : ℝ) : ℂ)‖ * ‖FW v ξ u‖ ≤ M * (CF * R) :=
            mul_le_mul hP0' hF0 (norm_nonneg _) hM0
        _ ≤ M * (CF * (64 ^ A * S)) := by gcongr
        _ ≤ 64 ^ A * (M * CF) * 16 * S := by
            have : 0 ≤ 64 ^ A * (M * CF) * S := by positivity
            nlinarith
    · unfold gT2
      refine (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl) |>.trans ?_
      rw [norm_mul, norm_mul (2 : ℂ), norm_mul, norm_mul, Complex.norm_ofNat]
      calc ‖((Phi2 (t / T) / T ^ 2 : ℝ) : ℂ)‖ * ‖FW v ξ u‖ +
            2 * (‖((Phi1 (t / T) / T : ℝ) : ℂ)‖ * ‖FW1 v ξ u‖) +
            ‖((phiT T t : ℝ) : ℂ)‖ * ‖FW2 v ξ u‖
          ≤ M / T ^ 2 * (CF * R) + 2 * (M / T * (CF * (2 / T) * R)) +
            M * (CF * (4 / T ^ 2) * R) := by gcongr
        _ = 9 * (M * CF) / T ^ 2 * R := by field_simp; ring
        _ ≤ 9 * (M * CF) / T ^ 2 * (64 ^ A * S) := by gcongr
        _ ≤ 64 ^ A * (M * CF) * 16 / T ^ 2 * S := by
            rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
            have : 0 ≤ 64 ^ A * (M * CF) * S := by positivity
            nlinarith
  · obtain ⟨h0, h1, h2⟩ := phiT_zero_outside hT0 ht
    have e0 : ((phiT T t : ℝ) : ℂ) = 0 := by unfold phiT; rw [h0]; simp
    constructor
    · unfold gT; rw [e0, zero_mul, norm_zero]; positivity
    · unfold gT2; rw [e0, h1, h2]; simp only [zero_div, ofReal_zero, zero_mul, mul_zero, add_zero,
        norm_zero]; positivity

/-! ## The far-term bound -/

/-- **M2.2: one off-diagonal `t`-integral.** -/
theorem farTerm_bound (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T x v ξ ω : ℝ, 1 ≤ T → 0 ≤ x → x ≤ 1 → |v| ≤ 1 → 0 < ξ →
      (‖∫ t in (T / 2)..(3 * T), gT T x v ξ t * cexp ((ω * t : ℝ) * I)‖ ≤
        C * T * (1 + ξ / T ^ 2) ^ (-A)) ∧
      (ω ≠ 0 → ‖∫ t in (T / 2)..(3 * T), gT T x v ξ t * cexp ((ω * t : ℝ) * I)‖ ≤
        C / (ω ^ 2 * T) * (1 + ξ / T ^ 2) ^ (-A)) := by
  obtain ⟨C, hC0, hC⟩ := gT2_bound A hA
  refine ⟨3 * C, by positivity, fun T x v ξ ω hT hx0 hx1 hv hξ => ?_⟩
  obtain ⟨hpk, hb⟩ := hC T x v ξ hT hx0 hx1 hv hξ
  have hT0 : 0 < T := by linarith
  have hAB : T / 2 ≤ 3 * T := by linarith
  set S := (1 + ξ / T ^ 2) ^ (-A)
  have hS : 0 ≤ S := Real.rpow_nonneg (by positivity) _
  have hlen : 3 * T - T / 2 ≤ 3 * T := by linarith
  constructor
  · refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := C * S) fun t _ => ?_).trans ?_
    · rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]; exact (hb t).1
    · rw [abs_of_nonneg (by linarith)]
      calc C * S * (3 * T - T / 2) ≤ C * S * (3 * T) := by gcongr
        _ = 3 * C * T * S := by ring
  · intro hω
    have hout : ∀ s : ℝ, s ∉ Icc (3 / 4 * T) (11 / 4 * T) →
        gT T x v ξ s = 0 ∧ gT1 T x v ξ s = 0 := by
      intro s hs
      obtain ⟨h0, h1, _⟩ := phiT_zero_outside hT0 hs
      have e0 : ((phiT T s : ℝ) : ℂ) = 0 := by unfold phiT; rw [h0]; simp
      refine ⟨by unfold gT; rw [e0, zero_mul], by unfold gT1; rw [e0, h1]; simp⟩
    have hA' := hout (T / 2) (fun h => by have := h.1; linarith)
    have hB' := hout (3 * T) (fun h => by have := h.2; linarith)
    have hi := ibp_twice hω hAB hpk.d0 hpk.d1 hpk.c2 hA'.1 hB'.1 hA'.2 hB'.2
    refine hi.trans ?_
    have hint : ∫ t in (T / 2)..(3 * T), ‖gT2 T x v ξ t‖ ≤ 3 * T * (C / T ^ 2 * S) := by
      refine (intervalIntegral.integral_mono_on hAB
        (hpk.c2.norm.intervalIntegrable _ _) intervalIntegrable_const fun t _ => (hb t).2).trans ?_
      rw [intervalIntegral.integral_const, smul_eq_mul]
      gcongr
    have hω2 : 0 < ω ^ 2 := by positivity
    calc (ω ^ 2)⁻¹ * ∫ t in (T / 2)..(3 * T), ‖gT2 T x v ξ t‖
        ≤ (ω ^ 2)⁻¹ * (3 * T * (C / T ^ 2 * S)) := by gcongr
      _ = 3 * C / (ω ^ 2 * T) * S := by field_simp

end RamanujanTau.SelbergKey4
