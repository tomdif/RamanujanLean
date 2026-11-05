/-
# Zero-free region, abstract layer (`EData`): continuation of `R(s)` and monotonicity of `‖F‖`

Port of `ZeroFreeRegion/Continuation.lean` (the Rankin–Selberg part) and
`ZeroFreeRegion/Monotone.lean` from `Δ` to the abstract normalized data `EigenformEdge.EData`
(edge at `Re s = 1`).  The Abel-summation machinery (`ZeroFreeRegion.abelI`, `LSeries_eq_abel`,
`Z1`) and the local identity `ZeroFreeRegion.localD_inv_eq_exp_tsum` are already generic and are
reused verbatim.
-/
import RamanujanTau.ZeroFreeRegion.Continuation
import RamanujanTau.ZeroFreeRegion.Monotone
import RamanujanTau.EigenformEdge.Edge

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanTau.GeneralZeros.ZFR

open Complex Filter Topology Finset
open RamanujanTau.EigenformEdge EData

variable [EData]

/-! ### `R(s)` continued to `Re s > 3/5` -/

lemma rs_part : ∃ C : ℝ, 0 ≤ C ∧
    ∀ N : ℕ, ‖(∑ k ∈ Icc 1 N, rsB k) - (rsc : ℂ) * N‖ ≤ C * (N : ℝ) ^ ((3 : ℝ) / 5) := by
  obtain ⟨C, hC0, hC⟩ := rs_partial'
  refine ⟨C, hC0, fun N => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have : (∑ k ∈ Icc 1 N, rsB k) - (rsc : ℂ) * N = ((∑ n ∈ Icc 1 N, rsb n - rsc * N : ℝ) : ℂ) := by
    simp [rsB]
  rw [this, Complex.norm_real, Real.norm_eq_abs]
  exact hC N hN

/-- `R(s)` continued to `Re s > 3/5`, `s ≠ 1`. -/
noncomputable def Rt (s : ℂ) : ℂ := rsc * s / (s - 1) + s * ZeroFreeRegion.abelI rsB rsc s

/-- `(s−1)R(s)`, continued to `Re s > 3/5`. -/
noncomputable def R1 (s : ℂ) : ℂ := rsc * s + (s - 1) * s * ZeroFreeRegion.abelI rsB rsc s

theorem differentiableAt_R1 {s : ℂ} (hs : 3 / 5 < s.re) : DifferentiableAt ℂ R1 s := by
  obtain ⟨C, hC0, hC⟩ := rs_part
  have := ZeroFreeRegion.differentiableAt_abelI hC0 (by norm_num) hC hs
  unfold R1; fun_prop

theorem differentiableAt_Rt {s : ℂ} (hs : 3 / 5 < s.re) (h1 : s ≠ 1) :
    DifferentiableAt ℂ Rt s := by
  obtain ⟨C, hC0, hC⟩ := rs_part
  have := ZeroFreeRegion.differentiableAt_abelI hC0 (by norm_num) hC hs
  have h1' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  unfold Rt
  fun_prop (disch := exact h1')

theorem Rt_eq {s : ℂ} (hs : 1 < s.re) : Rt s = RS s := by
  obtain ⟨C, hC0, hC⟩ := rs_part
  rw [RS, ZeroFreeRegion.LSeries_eq_abel hC0 (by norm_num) (by norm_num) hC hs (rs_summable hs),
    Rt]

theorem R1_eq {s : ℂ} (hs : 1 < s.re) : R1 s = (s - 1) * RS s := by
  have hs0 : s - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [← Rt_eq hs, Rt, R1]; field_simp

theorem norm_Rt_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, 3 / 5 < s.re →
    ‖Rt s‖ ≤ |rsc| * ‖s‖ / ‖s - 1‖ + ‖s‖ * (K / (s.re - 3 / 5)) := by
  obtain ⟨C, hC0, hC⟩ := rs_part
  refine ⟨C + |rsc|, by positivity, fun s hs => ?_⟩
  have hI := ZeroFreeRegion.norm_abelI_le hC0 (by norm_num) hC hs
  rw [Complex.norm_real, Real.norm_eq_abs] at hI
  calc ‖Rt s‖ ≤ ‖(rsc : ℂ) * s / (s - 1)‖ + ‖s * ZeroFreeRegion.abelI rsB rsc s‖ :=
        norm_add_le _ _
    _ ≤ |rsc| * ‖s‖ / ‖s - 1‖ + ‖s‖ * ((C + |rsc|) / (s.re - 3 / 5)) := by
        rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        gcongr

/-! ### Monotonicity of `‖F(σ)‖` -/

theorem Fp_eq_localD (t : ℝ) {p : ℕ} (hp : p.Prime) :
    ∃ α β : ℂ, α * β = 1 ∧ α + β = lam p ∧ 1 ≤ ‖α‖ ∧ ‖β‖ ≤ 1 ∧ ‖α‖ ^ 2 ≤ p ∧
      ∀ σ : ℝ, 1 < σ → Fp σ t p =
        (EdgeNonvanishing.localD α β (EdgeNonvanishing.ep p t) (EdgeNonvanishing.ep p (-t))
          (((p : ℝ) ^ (-σ) : ℝ) : ℂ))⁻¹ := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨α, β, hab, hs, hα1, hβ⟩ := EdgeNonvanishing.satake (lam p)
  have hα := alpha_sq_le hp hab hs hβ
  refine ⟨α, β, hab, hs, hα1, hβ, hα, fun σ hσ => ?_⟩
  set x : ℝ := (p : ℝ) ^ (-σ)
  have hX : (p : ℂ) ^ (-(σ : ℂ)) = (x : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity)]; push_cast; rfl
  have hZ : ∀ u : ℝ, (p : ℂ) ^ (-(sL σ u)) = EdgeNonvanishing.ep p u * x := by
    intro u
    rw [← hX, EdgeNonvanishing.ep, ← cpow_add _ _ hp0]; congr 1; simp [sL]
  have hY : ∀ u : ℝ, (p : ℂ) ^ (-(sR σ u)) = EdgeNonvanishing.ep p u ^ 2 * x := by
    intro u
    rw [← hX, EdgeNonvanishing.ep, sq, ← cpow_add _ _ hp0, ← cpow_add _ _ hp0]; congr 1
    simp [sR]; ring
  have hR : ∀ s : ℂ, 1 < s.re → fR s p =
      ((1 - (p : ℂ) ^ (-s)) ^ 2 * (1 - α ^ 2 * (p : ℂ) ^ (-s)) * (1 - β ^ 2 * (p : ℂ) ^ (-s)))⁻¹ :=
    fun s hs' => rs_local hs' hp hab hs hα hβ
  have hR0 := hR σ (by simpa using hσ)
  have hR1 := hR (sR σ t) (by simp [sR]; linarith)
  have hR2 := hR (sR σ (-t)) (by simp [sR]; linarith)
  rw [hX] at hR0
  rw [hY t] at hR1
  rw [hY (-t)] at hR2
  have hLa := L_local (sL σ t) p hab hs
  have hLb := L_local (sL σ (-t)) p hab hs
  rw [hZ t] at hLa
  rw [hZ (-t)] at hLb
  rw [Fp, hX, hLa, hLb, hR0, hR1, hR2, EdgeNonvanishing.localD]
  simp only [mul_inv, ← inv_pow, ← mul_assoc]
  ring

theorem norm_Fp_antitone (t : ℝ) {p : ℕ} (hp : p.Prime) {σ₁ σ₂ : ℝ} (h1 : 1 < σ₁)
    (h12 : σ₁ ≤ σ₂) : ‖Fp σ₂ t p‖ ≤ ‖Fp σ₁ t p‖ := by
  obtain ⟨α, β, hab, hs, hα1, hβ, hα, hF⟩ := Fp_eq_localD t hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hx : ∀ σ : ℝ, 1 < σ → ‖α‖ ^ 2 * (p : ℝ) ^ (-σ) < 1 := by
    intro σ hσ
    have hxp : (p : ℝ) * (p : ℝ) ^ (-σ) < 1 := by
      have : (p : ℝ) * (p : ℝ) ^ (-σ) = (p : ℝ) ^ (1 - σ) := by
        rw [Real.rpow_sub hp0, Real.rpow_one, Real.rpow_neg hp0.le, div_eq_mul_inv]
      rw [this]; exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hα (by positivity)) hxp
  have hee := EdgeNonvanishing.ep_mul hp t
  have hreal := EdgeNonvanishing.ep_add_real (p := p) t
  obtain ⟨hs1, he1⟩ := ZeroFreeRegion.localD_inv_eq_exp_tsum α β (EdgeNonvanishing.ep p t)
    (EdgeNonvanishing.ep p (-t)) (lam p) (2 * (EdgeNonvanishing.ep p t).re)
    ((p : ℝ) ^ (-σ₁)) (by positivity) hab hs hee hreal hα1 hβ (EdgeNonvanishing.ep_norm hp t)
    (EdgeNonvanishing.ep_norm hp (-t)) (hx σ₁ h1)
  obtain ⟨hs2, he2⟩ := ZeroFreeRegion.localD_inv_eq_exp_tsum α β (EdgeNonvanishing.ep p t)
    (EdgeNonvanishing.ep p (-t)) (lam p) (2 * (EdgeNonvanishing.ep p t).re)
    ((p : ℝ) ^ (-σ₂)) (by positivity) hab hs hee hreal hα1 hβ (EdgeNonvanishing.ep_norm hp t)
    (EdgeNonvanishing.ep_norm hp (-t)) (hx σ₂ (by linarith))
  rw [hF σ₁ h1, hF σ₂ (by linarith), he1, he2, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le,
    Real.exp_le_exp]
  have hxle : (p : ℝ) ^ (-σ₂) ≤ (p : ℝ) ^ (-σ₁) :=
    Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
  refine hs2.tsum_le_tsum (fun k => ?_) hs1
  have : 0 ≤ (1 + EdgeNonvanishing.pseq (lam p) k *
      EdgeNonvanishing.pseq (2 * (EdgeNonvanishing.ep p t).re) k) ^ 2 := sq_nonneg _
  have h0 : (0 : ℝ) ≤ (p : ℝ) ^ (-σ₂) := by positivity
  gcongr

theorem norm_Fval_antitone (t : ℝ) {σ₁ σ₂ : ℝ} (h1 : 1 < σ₁) (h12 : σ₁ ≤ σ₂) :
    ‖Fval σ₂ t‖ ≤ ‖Fval σ₁ t‖ := by
  have hN1 := (Fp_hasProd h1 t).norm
  have hN2 := (Fp_hasProd (lt_of_lt_of_le h1 h12) t).norm
  refine le_of_tendsto_of_tendsto' hN2 hN1 fun S => ?_
  exact Finset.prod_le_prod (fun p _ => norm_nonneg _)
    (fun p _ => norm_Fp_antitone t p.2 h1 h12)

theorem RS_ne_zero {s : ℂ} (hs : 1 < s.re) : RS s ≠ 0 := by
  have hF := one_le_norm_Fval hs (s.im / 2)
  intro h0
  have hsR : sR s.re (s.im / 2) = s := by
    apply Complex.ext <;> simp [sR]; ring
  have : Fval s.re (s.im / 2) = 0 := by
    rw [Fval, hsR, h0]; ring
  rw [this, norm_zero] at hF
  linarith

end RamanujanTau.GeneralZeros.ZFR
