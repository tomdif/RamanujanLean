/-
# Bruhat decomposition, part 1: real Möbius maps and the shape of `ff ∘ γ`

* `tauGL t : u ↦ t + u`, `gcGL c : u ↦ −1/(c²u)`, `dGL` the diagonal action of `GL(2,ℝ)`;
* `smul_eq_decomp`: for `γ = [[a,b],[c,d]]`, `c ≠ 0`: `γu = τ_{a/c}(ι_c(τ_{d/c} u))`;
* `ff_tau`: `ff(τ_t p) = e(ht) ff(p)`;
* `ff_smul_decomp`, `ft_smul_decomp`: `ft(γp) = 1_{strip}(a/c + Re ι_c τ_{d/c} z) e(ha/c) ff(ι_c τ_{d/c} p)`;
* `tsum_strip_shift`: `Σ_m 1_{[0,1)}(s + m) = 1`.
-/
import RamanujanTau.SCSProof.Bounds

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open MeasureTheory Set Complex
open UpperHalfPlane hiding I
open RamanujanTau.RankinError RamanujanTau.EisensteinReal RamanujanTau.EisensteinReal.Horo
open scoped MatrixGroups ENNReal Real ComplexConjugate

/-- Translation `u ↦ t + u`. -/
noncomputable def tauGL (t : ℝ) : GL (Fin 2) ℝ := affGL t 1 one_pos

lemma coe_tau_smul (t : ℝ) (u : ℍ) : ((tauGL t • u : ℍ) : ℂ) = t + u := by
  rw [tauGL, coe_affGL_smul]; simp

lemma tau_smul_re (t : ℝ) (u : ℍ) : (tauGL t • u).re = t + u.re := by
  change ((tauGL t • u : ℍ) : ℂ).re = _
  rw [coe_tau_smul]; simp

lemma tau_smul_im (t : ℝ) (u : ℍ) : (tauGL t • u).im = u.im := by
  change ((tauGL t • u : ℍ) : ℂ).im = _
  rw [coe_tau_smul]; simp

lemma tau_add (s t : ℝ) (u : ℍ) : tauGL s • (tauGL t • u) = tauGL (s + t) • u := by
  apply UpperHalfPlane.ext
  rw [coe_tau_smul, coe_tau_smul, coe_tau_smul]; push_cast; ring

lemma tau_zero (u : ℍ) : tauGL 0 • u = u := by
  apply UpperHalfPlane.ext; rw [coe_tau_smul]; simp

/-- Inversion `u ↦ −1/(c²u)`. -/
noncomputable def gcGL (c : ℝ) (hc : c ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, -1; c ^ 2, 0] (by
    rw [Matrix.det_fin_two_of]; simp; exact hc)

lemma gcGL_det (c : ℝ) (hc : c ≠ 0) : 0 < (gcGL c hc).det.val := by
  simp [gcGL, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two_of]
  positivity

lemma coe_gc_smul (c : ℝ) (hc : c ≠ 0) (u : ℍ) :
    ((gcGL c hc • u : ℍ) : ℂ) = -1 / ((c : ℂ) ^ 2 * u) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (gcGL_det c hc)]
  simp [gcGL, UpperHalfPlane.num, UpperHalfPlane.denom]

/-- Diagonal action of `GL(2,ℝ)`. -/
noncomputable def dGL (g : GL (Fin 2) ℝ) (p : ℍ × ℍ) : ℍ × ℍ := (g • p.1, g • p.2)

lemma measurePreserving_dGL (g : GL (Fin 2) ℝ) :
    MeasurePreserving (dGL g) (volume : Measure (ℍ × ℍ)) volume :=
  (measurePreserving_smul g (volume : Measure ℍ)).prod (measurePreserving_smul g volume)

/-- `dGL g` as a measurable equivalence. -/
noncomputable def dGLEquiv (g : GL (Fin 2) ℝ) : ℍ × ℍ ≃ᵐ ℍ × ℍ where
  toFun := dGL g
  invFun := dGL g⁻¹
  left_inv p := by simp [dGL]
  right_inv p := by simp [dGL]
  measurable_toFun := (measurePreserving_dGL g).measurable
  measurable_invFun := (measurePreserving_dGL g⁻¹).measurable

lemma integral_dGL (g : GL (Fin 2) ℝ) (F : ℍ × ℍ → ℂ) :
    ∫ q, F (dGL g q) = ∫ q, F q :=
  (measurePreserving_dGL g).integral_comp (dGLEquiv g).measurableEmbedding F

lemma lintegral_dGL (g : GL (Fin 2) ℝ) (F : ℍ × ℍ → ℝ≥0∞) :
    ∫⁻ q, F (dGL g q) = ∫⁻ q, F q :=
  (measurePreserving_dGL g).lintegral_comp_emb (dGLEquiv g).measurableEmbedding F

lemma dGL_tau_add (s t : ℝ) (p : ℍ × ℍ) :
    dGL (tauGL s) (dGL (tauGL t) p) = dGL (tauGL (s + t)) p := by
  simp [dGL, tau_add]

lemma dGL_tau_zero (p : ℍ × ℍ) : dGL (tauGL 0) p = p := by
  simp [dGL, tau_zero]

/-! ### The decomposition `γ = τ_{a/c} ι_c τ_{d/c}` -/

lemma smul_eq_decomp (γ : SL(2, ℤ)) (hc : ((γ 1 0 : ℤ) : ℝ) ≠ 0) (u : ℍ) :
    γ • u = tauGL ((γ 0 0 : ℝ) / γ 1 0) •
      (gcGL (γ 1 0 : ℝ) hc • (tauGL ((γ 1 1 : ℝ) / γ 1 0) • u)) := by
  apply UpperHalfPlane.ext
  rw [coe_smul_sl, coe_tau_smul, coe_gc_smul, coe_tau_smul]
  have hcC : ((γ 1 0 : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hc
  have hden := denom_ne_zero' γ u
  have hd := det_sl γ
  push_cast
  have h2 : ((γ 1 0 : ℂ) ^ 2 * ((γ 1 1 : ℂ) / γ 1 0 + u)) = (γ 1 0 : ℂ) * ((γ 1 0 : ℂ) * u + γ 1 1) := by
    field_simp; ring
  rw [h2, eq_comm, div_add_div _ _ hcC (mul_ne_zero hcC hden),
    div_eq_div_iff (mul_ne_zero hcC (mul_ne_zero hcC hden)) hden]
  linear_combination ((γ 1 0 : ℂ) * ((γ 1 0 : ℂ) * u + γ 1 1)) * hd

lemma dsmul_eq_decomp (γ : SL(2, ℤ)) (hc : ((γ 1 0 : ℤ) : ℝ) ≠ 0) (p : ℍ × ℍ) :
    dsmul γ p = dGL (tauGL ((γ 0 0 : ℝ) / γ 1 0))
      (dGL (gcGL (γ 1 0 : ℝ) hc) (dGL (tauGL ((γ 1 1 : ℝ) / γ 1 0)) p)) := by
  simp only [dsmul, dGL, smul_eq_decomp γ hc]

/-! ### Translation behaviour of `ff` -/

variable (P : Par)

lemma rel_tau (t : ℝ) (z w : ℍ) : rel (tauGL t • z) (tauGL t • w) = rel z w := by
  unfold rel
  rw [coe_tau_smul, tau_smul_re, tau_smul_im]
  push_cast; ring

lemma suppF_tau (t : ℝ) (p : ℍ × ℍ) : dGL (tauGL t) p ∈ suppF P ↔ p ∈ suppF P := by
  simp only [suppF, dGL, mem_setOf_eq, tau_smul_im, rel_tau]

lemma ff_tau (t : ℝ) (p : ℍ × ℍ) :
    ff P (dGL (tauGL t) p) = cexp (2 * π * I * P.h * t) * ff P p := by
  by_cases hp : p ∈ suppF P
  · have hq : dGL (tauGL t) p ∈ suppF P := (suppF_tau P t p).2 hp
    rw [ff, ff, if_pos hq, if_pos hp]
    simp only [dGL, tau_smul_re]
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  · have hq : dGL (tauGL t) p ∉ suppF P := fun h => hp ((suppF_tau P t p).1 h)
    rw [ff, ff, if_neg hq, if_neg hp, mul_zero]

lemma ff_tau_int (k : ℤ) (p : ℍ × ℍ) : ff P (dGL (tauGL k) p) = ff P p := by
  rw [ff_tau]
  have : cexp (2 * π * I * P.h * (k : ℝ)) = 1 := by
    rw [Complex.exp_eq_one_iff]; exact ⟨P.h * k, by push_cast; ring⟩
  rw [this, one_mul]

lemma dsmul_T_zpow (k : ℤ) (p : ℍ × ℍ) : dsmul (ModularGroup.T ^ k) p = dGL (tauGL k) p := by
  simp only [dsmul, dGL]
  congr 1 <;> apply UpperHalfPlane.ext <;> rw [coe_tau_smul, ModularGroup.coe_T_zpow_smul_eq] <;>
    push_cast <;> ring

/-! ### The strip sum -/

lemma tsum_strip_shift (s : ℝ) :
    ∑' m : ℤ, (Ico (0 : ℝ) 1).indicator (1 : ℝ → ℂ) (s + m) = 1 := by
  have hmem : ∀ m : ℤ, s + m ∈ Ico (0 : ℝ) 1 ↔ m = -⌊s⌋ := by
    intro m
    simp only [mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩
      have : ⌊s⌋ = -m := by
        rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
      omega
    · rintro rfl
      push_cast
      constructor <;> linarith [Int.floor_le s, Int.lt_floor_add_one s]
  rw [tsum_eq_single (-⌊s⌋) (fun m hm => indicator_of_notMem (fun h => hm ((hmem m).1 h)) _)]
  rw [indicator_of_mem ((hmem _).2 rfl)]
  rfl

lemma strip_iff (u : ℍ) : u ∈ strip ↔ u.re ∈ Ico (0 : ℝ) 1 := Iff.rfl

end RamanujanTau.SCSProof
