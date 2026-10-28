/-
# The `p + 1` Vélu kernels of the Tate curve (`TateKernels`)

For `p ≥ 5` prime, `ζ` a primitive `p`-th root of unity in `K` (char `0`) and any injective
`ι : K⟦t⟧ → L` into a field of characteristic `0`, with `E : y² = x³ + ι(A)x + ι(B)` the short model
of `Tate(t^p)`:

* `muKernel`: `μ_p = {P(ζ^k)}`, points `ι(eP(Xmu ζ k)), ι(eP(Ymu ζ k))`;
* `subKernel j`: `⟨ζ^j t⟩ = {P((ζ^j t)^k)}`, points `ι(Xsub ζ p j k), ι(Ysub ζ p j k)`;

are Vélu kernels (finite subgroups of order `p`) whose Vélu curves are `(veluQuot ζ p c).map ι`
(`muKernel_A'`, …, `kernels_curve`), pairwise distinct (`kernels_injective`).

**`tateKernels`**: `HeckeBridge.TateKernels p L ι ζ`.
-/
import RamanujanTau.TateAdd.Data
import RamanujanTau.HeckeBridge.Tate

set_option autoImplicit false

noncomputable section

namespace TateAdd

open PowerSeries TateQuot Finset

variable {K : Type*} [Field K] [CharZero K] {p : ℕ} [hp : Fact p.Prime] {ζ : K}
variable {L : Type*} [Field L] [CharZero L] [DecidableEq L] (ι : PowerSeries K →+* L)

local notation "Aₜ" => eP K p (Ash K)
local notation "Bₜ" => eP K p (Bsh K)

lemma eP_injective : Function.Injective (eP K p) := by
  intro F G h
  refine PowerSeries.ext fun n => ?_
  have := congrArg (coeff (p * n)) h
  simpa only [eP, coeff_expand_mul] using this

lemma rescale_injective {a : K} (ha : a ≠ 0) : Function.Injective (rescale a) := by
  intro F G h
  refine PowerSeries.ext fun n => ?_
  have := congrArg (coeff n) h
  rw [coeff_rescale, coeff_rescale] at this
  exact mul_left_cancel₀ (pow_ne_zero n ha) this

/-- `ι ∘ eP : K⟦q⟧ → L`. -/
def jmu : PowerSeries K →+* L := ι.comp (eP K p).toRingHom
/-- `ι ∘ (s ↦ ζ^j s)`. -/
def jsub (ζ : K) (j : ℕ) : PowerSeries K →+* L := ι.comp (rescale (ζ ^ j))

variable {ι} (hι : Function.Injective ι) (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
include hι hζ hp5

lemma hp2 : p ≠ 2 := by omega

/-- chord data of `μ_p`. -/
def muD : TorsData (ι Aₜ) (ι Bₜ) p :=
  TorsData.ofRing (jmu (p := p) ι) (hι.comp (eP_injective (p := p))) (Ash K) (Bsh K) (ι Aₜ) (ι Bₜ)
    rfl rfl (Xmu ζ) (Ymu ζ)
    (fun k h1 h2 => mu_on_curve hζ (mem_Ico.mpr ⟨h1, h2⟩))
    (fun k h1 h2 h => cc_Ymu_ne hζ (mem_Ico.mpr ⟨h1, h2⟩) (hp2 hι hζ hp5) (by rw [h, map_zero]))
    (fun k h1 h2 => Xmu_sym hζ (mem_Ico.mpr ⟨h1, h2⟩))
    (fun k h1 h2 => Ymu_sym hζ (hp2 hι hζ hp5) (mem_Ico.mpr ⟨h1, h2⟩))
    (fun a b h1 h2 h3 => Xmu_dist hζ h1 h2 h3)
    (fun a b h1 h2 h3 => mu_I hζ h1 h2 h3)

lemma jsub_A (j : ℕ) : jsub (L := L) ι ζ j (AshS K p) = ι Aₜ := by
  rw [jsub, RingHom.comp_apply, AshS_eq, rescale_expand hζ]
lemma jsub_B (j : ℕ) : jsub (L := L) ι ζ j (BshS K p) = ι Bₜ := by
  rw [jsub, RingHom.comp_apply, BshS_eq, rescale_expand hζ]

/-- chord data of `⟨ζ^j t⟩`. -/
def subD (j : ℕ) : TorsData (ι Aₜ) (ι Bₜ) p :=
  TorsData.ofRing (jsub ι ζ j) (hι.comp (rescale_injective (pow_ne_zero j (hζ.ne_zero hp.out.ne_zero))))
    (AshS K p) (BshS K p) (ι Aₜ) (ι Bₜ) (jsub_A hι hζ hp5 j) (jsub_B hι hζ hp5 j) (XB K p) (YB K p)
    (fun k h1 h2 => sub_on_curve (mem_Ico.mpr ⟨h1, h2⟩))
    (fun k h1 h2 => YB_ne (hp2 hι hζ hp5) h1 h2)
    (fun k h1 h2 => XB_sym (mem_Ico.mpr ⟨h1, h2⟩))
    (fun k h1 h2 => YB_sym (hp2 hι hζ hp5) h1 h2)
    (fun a b h1 h2 h3 => XB_dist (hp2 hι hζ hp5) h1 h2 h3)
    (fun a b h1 h2 h3 => sub_I h1 h2 h3)

/-- **The Vélu kernel `μ_p`.** -/
def muKernel : Velu.Kernel (ι Aₜ) (ι Bₜ) := (muD hι hζ hp5).kernel hp5
/-- **The Vélu kernel `⟨ζ^j t⟩`.** -/
def subKernel (j : ℕ) : Velu.Kernel (ι Aₜ) (ι Bₜ) := (subD hι hζ hp5 j).kernel hp5

theorem muKernel_A' : (muKernel hι hζ hp5).A' = ι (eP K p (veluA (Ash K) (Icc 1 (p / 2)) (Xmu ζ))) := by
  rw [muKernel, TorsData.kernel_A']
  exact (veluA_map (jmu (p := p) ι) _ _ _).symm
theorem muKernel_B' :
    (muKernel hι hζ hp5).B' = ι (eP K p (veluB (Ash K) (Bsh K) (Icc 1 (p / 2)) (Xmu ζ) (Ymu ζ))) := by
  rw [muKernel, TorsData.kernel_B']
  exact (veluB_map (jmu (p := p) ι) _ _ _ _ _).symm

theorem subKernel_A' (j : ℕ) :
    (subKernel hι hζ hp5 j).A' = ι (veluA (eP K p (Ash K)) (Icc 1 (p / 2)) (Xsub ζ p j)) := by
  rw [subKernel, TorsData.kernel_A', veluA_map]; rfl
theorem subKernel_B' (j : ℕ) :
    (subKernel hι hζ hp5 j).B' =
      ι (veluB (eP K p (Ash K)) (eP K p (Bsh K)) (Icc 1 (p / 2)) (Xsub ζ p j) (Ysub ζ p j)) := by
  rw [subKernel, TorsData.kernel_B', veluB_map]; rfl

/-- the `p + 1` kernels. -/
def kernels : Fin (p + 1) → Velu.Kernel (ι Aₜ) (ι Bₜ) :=
  Fin.cases (muKernel hι hζ hp5) fun j => subKernel hι hζ hp5 j

lemma kernels_card (c : Fin (p + 1)) : (kernels hι hζ hp5 c).G.card = p := by
  induction c using Fin.cases with
  | zero => exact (muD hι hζ hp5).kernel_card hp5
  | succ j => exact (subD hι hζ hp5 j).kernel_card hp5

omit hι hζ hp5 in
lemma short_map (a b : PowerSeries K) :
    (shortW a b).map ι = ((Velu.short (ι a) (ι b) : WeierstrassCurve.Affine L) : WeierstrassCurve L) := by
  ext <;> simp [shortW, Velu.short]

theorem kernels_curve (c : Fin (p + 1)) :
    ((kernels hι hζ hp5 c).curve : WeierstrassCurve L) = (veluQuot ζ p c).map ι := by
  induction c using Fin.cases with
  | zero =>
    simp only [kernels, Fin.cases_zero, veluQuot, Velu.Kernel.curve]
    rw [muKernel_A' hι hζ hp5, muKernel_B' hι hζ hp5, short_map]
  | succ j =>
    simp only [kernels, Fin.cases_succ, veluQuot, Velu.Kernel.curve]
    rw [subKernel_A' hι hζ hp5, subKernel_B' hι hζ hp5, short_map]

/-! ### Distinctness -/

/-- `x`-coordinates (in `K⟦t⟧`) of the points of kernel `c`. -/
def Xk (ζ : K) (p : ℕ) [Fact p.Prime] : Fin (p + 1) → ℕ → PowerSeries K :=
  Fin.cases (fun k => eP K p (Xmu ζ k)) fun j k => Xsub ζ p j k

omit hι hζ hp5 [CharZero L] [DecidableEq L] in
lemma cc_Xsub (j : ℕ) {k : ℕ} (hk1 : 1 ≤ k) (hk : k < p) (hp2 : p ≠ 2) :
    constantCoeff (Xsub ζ p j k) = 1 / 12 := by
  have hodd : p % 2 = 1 := (hp.out.eq_two_or_odd).resolve_left hp2
  rw [Xsub, ← coeff_zero_eq_constantCoeff, coeff_rescale, pow_zero, one_mul, XB, map_add,
    coeff_tB_lt (e := 0) (by norm_num) hk1 hk (by omega) (by omega), coeff_C, if_pos rfl, zero_add]

omit hι hζ hp5 [CharZero L] [DecidableEq L] in
lemma coeff1_Xsub (j : ℕ) {k : ℕ} (hk1 : 1 ≤ k) (hk : k < p) (hp5 : 5 ≤ p) :
    coeff 1 (Xsub ζ p j k) = ζ ^ j * (if k = 1 ∨ k = p - 1 then 1 else 0) := by
  rw [Xsub, coeff_rescale, pow_one, ← pow_one (ζ ^ j), ← pow_mul, mul_one, coeff_XB le_rfl]
  have hp2 : p ≠ 2 := by omega
  have hodd : p % 2 = 1 := (hp.out.eq_two_or_odd).resolve_left hp2
  congr 1
  split_ifs with h
  · rcases h with rfl | rfl
    · exact coeff_tB_k (e := 0) (by norm_num) le_rfl (by omega)
    · have := coeff_tB_pk (K := K) (p := p) (e := 0) (by norm_num) (k := p - 1) (by omega) (by omega)
        (by omega)
      rwa [show p - (p - 1) = 1 by omega, pow_zero] at this
  · exact coeff_tB_lt (e := 0) (by norm_num) hk1 hk (by omega) (by omega)

omit hι hp5 [CharZero L] [DecidableEq L] in
lemma cK0_ne {k : ℕ} (hk : k ∈ Ico 1 p) : cK 0 (ζ ^ k) ≠ 0 := by
  rw [cK0_eq]
  exact div_ne_zero (zeta_pow_ne_zero hζ k) (pow_ne_zero _ (sub_ne_zero.mpr (pow_ne_one_Ico hζ hk)))

omit hι [CharZero L] [DecidableEq L] in
lemma Xk_sep {c c' : Fin (p + 1)} (hc : c ≠ c') {k : ℕ} (hk1 : 1 ≤ k) (hk : k < p) :
    Xk ζ p c 1 ≠ Xk ζ p c' k := by
  have hp2 : p ≠ 2 := by omega
  have h1 : (1 : ℕ) ∈ Ico 1 p := mem_Ico.mpr ⟨le_rfl, by omega⟩
  have hkI : k ∈ Ico 1 p := mem_Ico.mpr ⟨hk1, hk⟩
  intro h
  induction c using Fin.cases with
  | zero =>
    induction c' using Fin.cases with
    | zero => exact hc rfl
    | succ j' =>
      have := congrArg constantCoeff h
      simp only [Xk, Fin.cases_zero, Fin.cases_succ, eP, constantCoeff_expand] at this
      rw [cc_Xmu hζ h1, cc_Xsub j' hk1 hk hp2, add_eq_right] at this
      exact cK0_ne hζ h1 this
  | succ j =>
    induction c' using Fin.cases with
    | zero =>
      have := congrArg constantCoeff h
      simp only [Xk, Fin.cases_zero, Fin.cases_succ, eP, constantCoeff_expand] at this
      rw [cc_Xmu hζ hkI, cc_Xsub j le_rfl (by omega) hp2, right_eq_add] at this
      exact cK0_ne hζ hkI this
    | succ j' =>
      have hjj : (j : ℕ) ≠ j' := fun e => hc (by rw [Fin.val_inj.mp e])
      have := congrArg (coeff 1) h
      simp only [Xk, Fin.cases_succ] at this
      rw [coeff1_Xsub j le_rfl (by omega) hp5, coeff1_Xsub j' hk1 hk hp5, if_pos (Or.inl rfl),
        mul_one] at this
      split_ifs at this
      · rw [mul_one] at this
        exact hjj (hζ.pow_inj j.isLt j'.isLt this)
      · rw [mul_zero] at this
        exact pow_ne_zero _ (hζ.ne_zero hp.out.ne_zero) this

lemma xc_kernels (c : Fin (p + 1)) {k : ℕ} (hk1 : 1 ≤ k) (hk : k < p) :
    ∃ Q ∈ (kernels hι hζ hp5 c).G, Q ≠ 0 ∧ Velu.xc Q = ι (Xk ζ p c k) := by
  induction c using Fin.cases with
  | zero =>
    refine ⟨(muD hι hζ hp5).pt k, ?_, (muD hι hζ hp5).pt_ne hk1 hk, ?_⟩
    · exact ((muD hι hζ hp5).mem_kernel hp5).mpr (Or.inr ⟨k, hk1, hk, rfl⟩)
    · rw [TorsData.xc_pt _ hk1 hk]; rfl
  | succ j =>
    refine ⟨(subD hι hζ hp5 j).pt k, ?_, (subD hι hζ hp5 j).pt_ne hk1 hk, ?_⟩
    · exact ((subD hι hζ hp5 j).mem_kernel hp5).mpr (Or.inr ⟨k, hk1, hk, rfl⟩)
    · rw [TorsData.xc_pt _ hk1 hk]; rfl

lemma mem_kernels (c : Fin (p + 1)) {Q : (Velu.short (ι Aₜ) (ι Bₜ)).Point}
    (hQ : Q ∈ (kernels hι hζ hp5 c).G) (h0 : Q ≠ 0) :
    ∃ k, 1 ≤ k ∧ k < p ∧ Velu.xc Q = ι (Xk ζ p c k) := by
  induction c using Fin.cases with
  | zero =>
    rcases ((muD hι hζ hp5).mem_kernel hp5).mp hQ with h | ⟨k, hk1, hk, rfl⟩
    · exact absurd h h0
    · exact ⟨k, hk1, hk, by rw [TorsData.xc_pt _ hk1 hk]; rfl⟩
  | succ j =>
    rcases ((subD hι hζ hp5 j).mem_kernel hp5).mp hQ with h | ⟨k, hk1, hk, rfl⟩
    · exact absurd h h0
    · exact ⟨k, hk1, hk, by rw [TorsData.xc_pt _ hk1 hk]; rfl⟩

theorem kernels_injective : Function.Injective fun c => (kernels hι hζ hp5 c).G := by
  intro c c' h
  by_contra hc
  obtain ⟨Q, hQ, hQ0, hx⟩ := xc_kernels hι hζ hp5 c (k := 1) le_rfl (by omega)
  have hQ' : Q ∈ (kernels hι hζ hp5 c').G := by simpa only [h] using hQ
  obtain ⟨k, hk1, hk, hx'⟩ := mem_kernels hι hζ hp5 c' hQ' hQ0
  exact Xk_sep hζ hp5 hc hk1 hk (hι (hx.symm.trans hx'))

/-- **The Tate addition theorem, in the form needed by `HeckeBridge`**: for `p ≥ 5`, the `p + 1`
explicit kernels `μ_p`, `⟨ζ^j t⟩` are Vélu kernels of order `p` with Vélu quotients
`veluQuot ζ p`. -/
theorem tateKernels : HeckeBridge.TateKernels p L ι ζ :=
  HeckeBridge.tateKernels_of_kernels p ι ζ (kernels hι hζ hp5) (kernels_card hι hζ hp5)
    (kernels_injective hι hζ hp5) (kernels_curve hι hζ hp5)

end TateAdd
