/-
# Bruhat decomposition, part 5: assembly

`norm_tsum_Iγ_le`: `‖Σ_γ I(γ)‖ ≤ 2 ∫⁻‖ft‖ + Σ_{0<|c|≤K₂} ‖S(h,h;|c|)‖ · 64ε³/(|c|Y)`, `K₂ = ⌈2/Y⌉`.
-/
import RamanujanTau.SCSProof.Bruhat4

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open MeasureTheory Set Complex
open UpperHalfPlane hiding I
open RamanujanTau.RankinError RamanujanTau.EisensteinReal RamanujanTau.EisensteinReal.Horo
open RamanujanTau.TauBound
open scoped MatrixGroups ENNReal Real ComplexConjugate

variable (P : Par)

open Classical in
/-- The layer functional on `ℤ × ℤ` (zero off the coprime pairs). -/
noncomputable def Rt (x : ℤ × ℤ) : ℂ :=
  if h : x ∈ copSet then ∫ q, ff P q * conj (ft P (dsmul (mat ⟨x, h⟩) q)) else 0

lemma norm_Rt_le (x : ℤ × ℤ) : ‖Rt P x‖ ≤ (∫⁻ q, ‖ft P q‖ₑ).toReal := by
  unfold Rt; split_ifs with h
  · exact norm_R_le P _
  · simp

lemma Rt_eq (a c : ℤ) (hc : c ≠ 0) (h : Int.gcd a c = 1) :
    Rt P (a, c) = ph P c a * Kint P (c : ℝ) (by exact_mod_cast hc) ((a : ℝ) / c) := by
  have hmem : (a, c) ∈ copSet := h
  unfold Rt
  rw [dif_pos hmem]
  have hc' : (((mat ⟨(a, c), hmem⟩) 1 0 : ℤ) : ℝ) ≠ 0 := by
    rw [mat_apply_10]; exact_mod_cast hc
  rw [Rg_eq P _ hc']
  simp only [mat_apply_00, mat_apply_10, mat_apply_11]
  rfl

lemma Rt_noncop (a c : ℤ) (h : Int.gcd a c ≠ 1) : Rt P (a, c) = 0 := by
  unfold Rt; rw [dif_neg (show (a, c) ∉ copSet from h)]

/-! ### Summability -/

lemma summable_slEquiv : Summable fun x : copSet × ℤ => Iγ P (mat x.1 * ModularGroup.T ^ x.2) :=
  (slEquiv.symm.summable_iff (f := Iγ P)).2 (summable_Iγ P)

lemma tsum_Iγ_eq_copSet :
    ∑' γ, Iγ P γ = ∑' p : copSet, ∫ q, ff P q * conj (ft P (dsmul (mat p) q)) := by
  rw [← slEquiv.symm.tsum_eq (Iγ P)]
  change ∑' x : copSet × ℤ, Iγ P (mat x.1 * ModularGroup.T ^ x.2) = _
  rw [(summable_slEquiv P).tsum_prod' (fun p => (summable_slEquiv P).comp_injective
    (Prod.mk_right_injective p))]
  exact tsum_congr fun p => (hasSum_right_T P (mat p)).tsum_eq

lemma summable_copSet : Summable fun p : copSet => ∫ q, ff P q * conj (ft P (dsmul (mat p) q)) := by
  have := (summable_slEquiv P).prod
  refine this.congr fun p => (hasSum_right_T P (mat p)).tsum_eq

lemma support_Rt : Function.support (Rt P) ⊆ Set.range (Subtype.val : copSet → ℤ × ℤ) := by
  intro x hx
  by_contra h
  apply hx
  unfold Rt
  rw [dif_neg (fun hm => h ⟨⟨x, hm⟩, rfl⟩)]

lemma Rt_val (p : copSet) : Rt P p.1 = ∫ q, ff P q * conj (ft P (dsmul (mat p) q)) := by
  unfold Rt; rw [dif_pos p.2]

lemma summable_Rt : Summable (Rt P) := by
  have := (Subtype.val_injective.summable_iff (f := Rt P) (fun x hx =>
    Function.notMem_support.1 (fun h => hx (support_Rt P h)))).1
  refine this ?_
  exact (summable_copSet P).congr fun p => (Rt_val P p).symm

lemma tsum_Iγ_eq_Rt : ∑' γ, Iγ P γ = ∑' x, Rt P x := by
  rw [tsum_Iγ_eq_copSet, ← Subtype.val_injective.tsum_eq (support_Rt P)]
  exact tsum_congr fun p => (Rt_val P p).symm

/-! ### The layers -/

/-- `T(c) = Σ_a R̃(a,c)`. -/
noncomputable def Tl (c : ℤ) : ℂ := ∑' a : ℤ, Rt P (a, c)

lemma summable_swap : Summable fun y : ℤ × ℤ => Rt P (y.2, y.1) :=
  ((Equiv.prodComm ℤ ℤ).summable_iff (f := Rt P)).2 (summable_Rt P)

lemma tsum_Rt_eq : ∑' x, Rt P x = ∑' c, Tl P c := by
  rw [← (Equiv.prodComm ℤ ℤ).tsum_eq (Rt P)]
  change ∑' y : ℤ × ℤ, Rt P (y.2, y.1) = _
  rw [(summable_swap P).tsum_prod' (fun c => (summable_swap P).comp_injective
    (Prod.mk_right_injective c))]
  rfl

lemma summable_Tl : Summable (Tl P) := by
  have := (summable_swap P).prod
  exact this

lemma summable_layer (c : ℤ) : Summable fun a : ℤ => Rt P (a, c) := by
  have := (summable_swap P).comp_injective (Prod.mk_right_injective c)
  exact this

/-- The `c = 0` layer. -/
lemma norm_Tl_zero : ‖Tl P 0‖ ≤ 2 * (∫⁻ q, ‖ft P q‖ₑ).toReal := by
  unfold Tl
  rw [tsum_eq_sum (s := {1, -1}) (fun a ha => ?_)]
  · refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_pair (by norm_num)]
    linarith [norm_Rt_le P (1, 0), norm_Rt_le P (-1, 0)]
  · refine Rt_noncop P a 0 ?_
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
    rw [Int.gcd_zero_right]
    intro h1
    rcases Int.natAbs_eq a with h2 | h2 <;> rw [h1] at h2 <;> simp_all

end RamanujanTau.SCSProof
