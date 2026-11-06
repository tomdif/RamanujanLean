/-
# The two-point invariant for the two-sided problem: `Ψ_{a,b}(z,w) = (z − w̄)¹² Δ(az) conj Δ(bw)`

* `scl_smul`: for `a ∣ γ₁₀`, `a·(γz) = γ'_a(az)` with `γ'_a = [[A, aB],[C/a, D]] ∈ SL₂(ℤ)`;
* `Delta_scl_smul`: `Δ(a·γz) = (Cz+D)¹² Δ(az)` for `a ∣ C`;
* **`PsiAB_smul`**: `Ψ_{a,b}(γz, γw) = Ψ_{a,b}(z, w)` for `a ∣ C` and `b ∣ C` (e.g. `γ ∈ Γ₀(ab)`);
* **`norm_PsiAB_le`**: `‖Ψ_{a,b}(z,w)‖ ≤ M (ab)^{−6} (|z − w̄|²/(Im z Im w))⁶`, `M` independent of `a, b`.
-/
import RamanujanTau.SCS2Coprime.Gamma0
import RamanujanTau.SCSProof.TwoPoint

set_option autoImplicit false

namespace RamanujanTau.SCS2Coprime

open Complex ModularForm
open UpperHalfPlane hiding I
open scoped MatrixGroups ComplexConjugate
open RamanujanTau.RankinSelberg RamanujanTau.SCSProof

/-- `z ↦ a z` on `ℍ` (`a ∈ ℕ⁺`). -/
def scl (a : ℕ+) (z : ℍ) : ℍ := ⟨(a : ℂ) * z, by
  have : (0 : ℝ) < (a : ℝ) := by exact_mod_cast a.pos
  simpa [Complex.mul_im] using mul_pos this z.im_pos⟩

lemma scl_coe (a : ℕ+) (z : ℍ) : ((scl a z : ℍ) : ℂ) = (a : ℂ) * z := rfl

lemma scl_im (a : ℕ+) (z : ℍ) : (scl a z).im = a * z.im := by
  show ((a : ℂ) * z).im = _; simp [Complex.mul_im]

/-- `γ'_a = [[A, aB],[C/a, D]]` (for `a ∣ C`). -/
def gScl (a : ℕ+) (γ : SL(2, ℤ)) (h : (a : ℤ) ∣ γ 1 0) : SL(2, ℤ) :=
  ⟨!![γ 0 0, a * γ 0 1; γ 1 0 / a, γ 1 1], by
    have hd := γ.2
    rw [Matrix.det_fin_two] at hd
    rw [Matrix.det_fin_two_of]
    have e : (a : ℤ) * (γ 1 0 / a) = γ 1 0 := Int.mul_ediv_cancel' h
    linear_combination hd - γ 0 1 * e⟩

lemma gScl_10 (a : ℕ+) (γ : SL(2, ℤ)) (h : (a : ℤ) ∣ γ 1 0) :
    ((((gScl a γ h) 1 0 : ℤ) : ℂ)) * (a : ℂ) = (γ 1 0 : ℂ) := by
  have e : (γ 1 0 / a) * (a : ℤ) = γ 1 0 := Int.ediv_mul_cancel h
  show (((γ 1 0 / a : ℤ) : ℂ)) * ((a : ℕ) : ℂ) = _
  exact_mod_cast e

lemma scl_smul (a : ℕ+) (γ : SL(2, ℤ)) (h : (a : ℤ) ∣ γ 1 0) (z : ℍ) :
    scl a (γ • z) = gScl a γ h • scl a z := by
  apply UpperHalfPlane.ext
  rw [scl_coe, coe_smul_sl, coe_smul_sl, scl_coe]
  have hz := denom_ne_zero' γ z
  have e10 := gScl_10 a γ h
  have h00 : (((gScl a γ h) 0 0 : ℤ) : ℂ) = γ 0 0 := rfl
  have h01 : (((gScl a γ h) 0 1 : ℤ) : ℂ) = (a : ℂ) * γ 0 1 := by
    show (((a : ℤ) * γ 0 1 : ℤ) : ℂ) = _; push_cast; rfl
  have h11 : (((gScl a γ h) 1 1 : ℤ) : ℂ) = γ 1 1 := rfl
  rw [h00, h01, h11]
  have hden : (((gScl a γ h) 1 0 : ℤ) : ℂ) * ((a : ℂ) * z) + γ 1 1 = (γ 1 0 : ℂ) * z + γ 1 1 := by
    rw [← e10]; ring
  rw [hden]
  field_simp

lemma Delta_scl_smul (a : ℕ+) (γ : SL(2, ℤ)) (h : (a : ℤ) ∣ γ 1 0) (z : ℍ) :
    Δf (scl a (γ • z)) = ((γ 1 0 : ℂ) * z + γ 1 1) ^ 12 * Δf (scl a z) := by
  rw [scl_smul a γ h, Delta_smul, scl_coe]
  have e10 := gScl_10 a γ h
  have h11 : (((gScl a γ h) 1 1 : ℤ) : ℂ) = γ 1 1 := rfl
  rw [h11]
  congr 2
  rw [← e10]; ring

/-- `Ψ_{a,b}(z,w) = (z − w̄)¹² Δ(az) conj Δ(bw)`. -/
noncomputable def PsiAB (a b : ℕ+) (z w : ℍ) : ℂ :=
  ((z : ℂ) - conj (w : ℂ)) ^ 12 * Δf (scl a z) * conj (Δf (scl b w))

/-- **Invariance** under every `γ` with `a ∣ γ₁₀` and `b ∣ γ₁₀` (in particular `Γ₀(ab)`). -/
theorem PsiAB_smul (a b : ℕ+) (γ : SL(2, ℤ)) (ha : (a : ℤ) ∣ γ 1 0) (hb : (b : ℤ) ∣ γ 1 0)
    (z w : ℍ) : PsiAB a b (γ • z) (γ • w) = PsiAB a b z w := by
  unfold PsiAB
  rw [smul_sub_conj, Delta_scl_smul a γ ha, Delta_scl_smul b γ hb]
  have hz := denom_ne_zero' γ z
  have hw := denom_ne_zero' γ w
  have hw' : conj ((γ 1 0 : ℂ) * w + γ 1 1) ≠ 0 := (map_ne_zero _).2 hw
  have hz' : (z : ℂ) * γ 1 0 + γ 1 1 ≠ 0 := by rw [mul_comm]; exact hz
  rw [div_pow, map_mul, map_pow]
  field_simp

theorem PsiAB_smul_Gamma0 (a b : ℕ+) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 (a * b))
    (z w : ℍ) : PsiAB a b (γ • z) (γ • w) = PsiAB a b z w := by
  have h := (mem_Gamma0_iff _ γ).1 hγ
  push_cast at h
  exact PsiAB_smul a b γ (dvd_trans (dvd_mul_right _ _) h) (dvd_trans (dvd_mul_left _ _) h) z w

/-- **Size**: `‖Ψ_{a,b}(z,w)‖ ≤ M (ab)^{−6} (|z − w̄|²/(Im z Im w))⁶`. -/
theorem norm_PsiAB_le : ∃ M : ℝ, 0 ≤ M ∧ ∀ (a b : ℕ+) (z w : ℍ),
    ‖PsiAB a b z w‖ ≤ M / ((a : ℝ) * b) ^ 6 *
      (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ 6 := by
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound (CuspForm.discriminant : CuspForm 𝒮ℒ 12)
  have hC0 : 0 ≤ C := by
    have := hC UpperHalfPlane.I
    exact le_trans (norm_nonneg _) (by simpa using this)
  have hb6 : ∀ u : ℍ, ‖Δf u‖ ≤ C / u.im ^ 6 := fun u => by
    have := hC u
    have e12 : (((12 : ℤ) : ℝ) / 2) = 6 := by norm_num
    rw [e12] at this
    rw [← Real.rpow_natCast]; simpa using this
  refine ⟨C ^ 2, by positivity, fun a b z w => ?_⟩
  have hzi := z.im_pos
  have hwi := w.im_pos
  have ha : (0 : ℝ) < a := by exact_mod_cast a.pos
  have hb : (0 : ℝ) < b := by exact_mod_cast b.pos
  have hz' := hb6 (scl a z)
  have hw' := hb6 (scl b w)
  rw [scl_im] at hz' hw'
  unfold PsiAB
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_conj]
  have hn : ‖(z : ℂ) - conj (w : ℂ)‖ ^ 12 =
      Complex.normSq ((z : ℂ) - conj (w : ℂ)) ^ 6 := by
    rw [Complex.normSq_eq_norm_sq, ← pow_mul]
  rw [hn]
  calc Complex.normSq ((z : ℂ) - conj (w : ℂ)) ^ 6 * ‖Δf (scl a z)‖ * ‖Δf (scl b w)‖
      ≤ Complex.normSq ((z : ℂ) - conj (w : ℂ)) ^ 6 * (C / (a * z.im) ^ 6) *
          (C / (b * w.im) ^ 6) := by gcongr
    _ = C ^ 2 / ((a : ℝ) * b) ^ 6 *
          (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ 6 := by
        field_simp

end RamanujanTau.SCS2Coprime
