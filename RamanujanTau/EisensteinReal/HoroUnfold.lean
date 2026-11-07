/-
# Unfolding the horocycle integral of a lattice-point count (Route B)

For the rectangle `R = {α ≤ Re w < β, A ≤ Im w}` put `N_R(z) = #{γ ∈ SL₂(ℤ) : γz ∈ R}`
(`cnt`). We compute its horocycle mean `∫₀¹ N_R(x + iy) dx` (`horo`):

* `slEquiv`: `SL₂(ℤ) ≃ {(a,c) coprime} × ℤ`, `γ = M(a,c)·Tᵏ` (left column `(a,c)`).
* `lintegral_cnt_eq`: `∫₀¹ ∑_γ F(γ(x+iy)) dx = ∑_{(a,c)} ∫_ℝ F(M(a,c)(x+iy)) dx`.
* `re_mat_smul`, `im_mat_smul`: after the shift `x ↦ x − d/c`,
  `M(a,c)(x+iy) = a/c − 1/(c²(x+iy))`.
-/
import RamanujanTau.EisensteinReal.HoroArith
import RamanujanTau.RankinSelberg.Parseval
import Mathlib.NumberTheory.Modular
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure

set_option autoImplicit false

namespace RamanujanTau.EisensteinReal.Horo

open Finset Real Filter Topology MeasureTheory ModularGroup Matrix
open RamanujanTau.RankinSelberg
open UpperHalfPlane hiding I
open scoped MatrixGroups ENNReal

/-! ### Coset parametrization -/

/-- Coprime pairs `(a, c)`. -/
def copSet : Set (ℤ × ℤ) := {p | Int.gcd p.1 p.2 = 1}

/-- The matrix `M(a,c) = [[a, -gcdB a c], [c, gcdA a c]] ∈ SL₂(ℤ)` with left column `(a,c)`. -/
def mat (p : copSet) : SL(2, ℤ) :=
  ⟨!![p.1.1, -Int.gcdB p.1.1 p.1.2; p.1.2, Int.gcdA p.1.1 p.1.2], by
    have h := Int.gcd_eq_gcd_ab p.1.1 p.1.2
    rw [show Int.gcd p.1.1 p.1.2 = 1 from p.2] at h
    rw [Matrix.det_fin_two_of]
    push_cast at h
    linarith⟩

lemma mat_apply_00 (p : copSet) : (mat p) 0 0 = p.1.1 := rfl
lemma mat_apply_01 (p : copSet) : (mat p) 0 1 = -Int.gcdB p.1.1 p.1.2 := rfl
lemma mat_apply_10 (p : copSet) : (mat p) 1 0 = p.1.2 := rfl
lemma mat_apply_11 (p : copSet) : (mat p) 1 1 = Int.gcdA p.1.1 p.1.2 := rfl

lemma col_coprime (γ : SL(2, ℤ)) : ((γ 0 0, γ 1 0) : ℤ × ℤ) ∈ copSet := by
  show Int.gcd (γ 0 0) (γ 1 0) = 1
  refine Int.isCoprime_iff_gcd_eq_one.mp ⟨γ 1 1, -γ 0 1, ?_⟩
  have h := γ.det_coe
  rw [Matrix.det_fin_two] at h
  linarith

/-- Left column of a matrix in `SL₂(ℤ)`. -/
def col (γ : SL(2, ℤ)) : copSet := ⟨(γ 0 0, γ 1 0), col_coprime γ⟩

lemma T_zpow_apply (k : ℤ) (i j : Fin 2) :
    (T ^ k) i j = (!![1, k; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) i j := by
  rw [← coe_T_zpow]

lemma mul_T_zpow_00 (g : SL(2, ℤ)) (k : ℤ) : (g * T ^ k) 0 0 = g 0 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    T_zpow_apply, T_zpow_apply]
  simp

lemma mul_T_zpow_10 (g : SL(2, ℤ)) (k : ℤ) : (g * T ^ k) 1 0 = g 1 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    T_zpow_apply, T_zpow_apply]
  simp

lemma col_mul_T_zpow (g : SL(2, ℤ)) (k : ℤ) : col (g * T ^ k) = col g := by
  apply Subtype.ext
  simp [col, mul_T_zpow_00, mul_T_zpow_10]

lemma col_mat (p : copSet) : col (mat p) = p := by
  apply Subtype.ext
  simp [col, mat_apply_00, mat_apply_10]

/-- If `N ∈ SL₂(ℤ)` has left column `(1,0)` then `N = T^{N₀₁}`. -/
lemma eq_T_zpow_of_col {N : SL(2, ℤ)} (h0 : N 0 0 = 1) (h1 : N 1 0 = 0) :
    N = T ^ (N 0 1) := by
  have hd := N.det_coe
  rw [Matrix.det_fin_two, h0, h1] at hd
  have h11 : N 1 1 = 1 := by linarith
  ext i j
  fin_cases i <;> fin_cases j <;> simp [T_zpow_apply, h0, h1, h11]

lemma inv_mul_col (γ : SL(2, ℤ)) :
    ((mat (col γ))⁻¹ * γ) 0 0 = 1 ∧ ((mat (col γ))⁻¹ * γ) 1 0 = 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  have h := Int.gcd_eq_gcd_ab (γ 0 0) (γ 1 0)
  rw [show Int.gcd (γ 0 0) (γ 1 0) = 1 from col_coprime γ] at h
  simp only [Matrix.adjugate_fin_two, mat, col, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
  constructor
  · push_cast at h; linarith
  · ring

/-- `SL₂(ℤ) ≃ {(a,c) coprime} × ℤ`, `γ ↦ (left column, k)` with `γ = M(a,c)·Tᵏ`. -/
def slEquiv : SL(2, ℤ) ≃ copSet × ℤ where
  toFun γ := (col γ, ((mat (col γ))⁻¹ * γ) 0 1)
  invFun q := mat q.1 * T ^ q.2
  left_inv γ := by
    obtain ⟨h0, h1⟩ := inv_mul_col γ
    have := eq_T_zpow_of_col h0 h1
    simp only
    rw [← this, mul_inv_cancel_left]
  right_inv q := by
    obtain ⟨p, k⟩ := q
    simp only [col_mul_T_zpow, col_mat, inv_mul_cancel_left, Prod.mk.injEq, true_and]
    rw [T_zpow_apply]; simp

instance : Countable SL(2, ℤ) := slEquiv.injective.countable

/-! ### The unfolding identity -/

/-- `∫_ℝ f = ∑_{n ∈ ℤ} ∫₀¹ f(x + n)`. -/
lemma lintegral_eq_tsum_Ioc (f : ℝ → ℝ≥0∞) :
    ∫⁻ x, f x = ∑' n : ℤ, ∫⁻ x in Set.Ioc (0 : ℝ) 1, f (x + n) := by
  rw [← setLIntegral_univ, ← iUnion_Ioc_add_intCast (0 : ℝ),
    lintegral_iUnion (fun _ => measurableSet_Ioc) (Set.pairwise_disjoint_Ioc_add_intCast (0 : ℝ))]
  refine tsum_congr fun n => ?_
  rw [← lintegral_indicator measurableSet_Ioc, ← lintegral_indicator measurableSet_Ioc,
    ← lintegral_add_right_eq_self (μ := volume) _ (n : ℝ)]
  congr 1
  funext x
  simp only [Set.indicator, Set.mem_Ioc, zero_add]
  congr 1
  apply propext
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

lemma hp_add {y : ℝ} (hy : 0 < y) (x : ℝ) (k : ℤ) : T ^ k • hp hy x = hp hy (x + k) := by
  apply UpperHalfPlane.ext
  rw [coe_T_zpow_smul_eq, hp_coe, hp_coe]
  push_cast; ring

lemma measurable_smul_hp {y : ℝ} (hy : 0 < y) (g : SL(2, ℤ)) :
    Continuous fun x : ℝ => g • hp hy x := by
  have : (fun x : ℝ => g • hp hy x) = fun x => (g : GL (Fin 2) ℝ) • hp hy x := by
    funext x; exact ModularGroup.sl_moeb g _
  rw [this]
  exact (continuous_const_smul _).comp (continuous_hp hy)

/-- **Unfolding.** For measurable `F ≥ 0` on `ℍ`:
`∫₀¹ ∑_{γ ∈ SL₂(ℤ)} F(γ(x+iy)) dx = ∑_{(a,c) coprime} ∫_ℝ F(M(a,c)(x+iy)) dx`. -/
theorem lintegral_unfold {y : ℝ} (hy : 0 < y) {F : ℍ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x in Set.Ioc (0 : ℝ) 1, ∑' γ : SL(2, ℤ), F (γ • hp hy x) =
      ∑' p : copSet, ∫⁻ x, F (mat p • hp hy x) := by
  rw [lintegral_tsum (f := fun (γ : SL(2, ℤ)) (x : ℝ) => F (γ • hp hy x))
    (fun γ => (hF.comp (measurable_smul_hp hy γ).measurable).aemeasurable)]
  rw [← slEquiv.symm.tsum_eq, ENNReal.tsum_prod']
  refine tsum_congr fun p => ?_
  rw [lintegral_eq_tsum_Ioc]
  refine tsum_congr fun k => ?_
  refine setLIntegral_congr_fun measurableSet_Ioc (fun x _ => ?_)
  simp only [slEquiv, Equiv.coe_fn_symm_mk, mul_smul, hp_add]

end RamanujanTau.EisensteinReal.Horo

#print axioms RamanujanTau.EisensteinReal.Horo.slEquiv
#print axioms RamanujanTau.EisensteinReal.Horo.lintegral_unfold
