import RamanujanTau.ThetaLift.LiftForm
import RamanujanTau.ThetaLift.KernelCR

/-!
# Modularity of the Shimura lifts and Theorem A

This file proves `AADRaisedModularity`, and so `AADModularity` and Theorem A, with no hypothesis.
-/

set_option autoImplicit false

namespace RamanujanTau.ThetaLift
open Complex
open UpperHalfPlane hiding I
open ModularForm CongruenceSubgroup Rademacher
open RamanujanTau.TheoremA RamanujanTau.TheoremA.HalfIntegral RamanujanTau.TheoremA.SignLattice BoylanWebb
open scoped Real MatrixGroups Topology

noncomputable section

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- The double sum is holomorphic. -/
theorem lamSum_differentiableAt (h5 : 5 ≤ ℓ) {a : PowerSeries ℤ} (G : CuspForm 𝒮ℒ (kPrime ℓ))
    (hG : PowerSeries.map (Int.castRingHom ℂ) a = qExpansion (1 : ℝ) G) {t : ℕ} (hN : 0 < t)
    (hsf : Squarefree t) (ht : 24 ∣ t + jj ℓ) {w : ℂ} (hw : 0 < w.im) :
    DifferentiableAt ℂ
      (fun w : ℂ => lamSum G (jj ℓ) (N := t) (jN t) (halfWt ℓ) w.re w.im) w := by
  obtain ⟨hj, ht2, ht3, hNj, hjw, hk, hlam, hneg⟩ := arithData (ℓ := ℓ) h5 ht
  set A : ℕ → ℤ := fun m => (coordOf ℓ a).coeff m with hAdef
  have hA : ∀ m, cA G (jj ℓ) m = ((A m : ℤ) : ℂ) := by
    intro m
    have h := qExp_hP G (jj ℓ) hG
    have e : coordOf ℓ a = a * MockTheta5.JTP.partitionGF ^ jj ℓ := by
      simp [coordOf]
    unfold cA
    rw [h, PowerSeries.coeff_map]
    simp [hAdef, e]
  obtain ⟨C, E, hAb⟩ := coord_bound G hj hA
  obtain ⟨Cb, hCb0, hCb⟩ := sum_bound (A := A) hlam hAb t (jj ℓ)
  set b : ℕ → ℂ := bC (halfWt ℓ) t (jj ℓ) A with hb
  have hbb : ∀ n : ℕ, 1 ≤ n → ‖b n‖ ≤ Cb * (n : ℝ) ^ (halfWt ℓ + 2 * E) := fun n hn =>
    (norm_sum_le _ _).trans (hCb n hn)
  have hqeq : ∀ s : ℂ, qN t s.re s.im = cexp (2 * π * I * t * s) := by
    intro s
    unfold qN
    rw [Complex.re_add_im]
  have hq1 : ‖cexp (2 * π * I * t * w)‖ < 1 := by
    rw [← hqeq]
    exact norm_qN_lt hN hw w.re
  have hd : DifferentiableAt ℂ (qS b) (cexp (2 * π * I * t * w)) := by
    refine (qS_diff b hbb).differentiableAt (Metric.isOpen_ball.mem_nhds ?_)
    simpa using hq1
  have hcomp : DifferentiableAt ℂ (fun s : ℂ => (chiZ (t : ℤ) : ℂ) * qS b (cexp (2 * π * I * t * s))) w := by
    have hinner : DifferentiableAt ℂ (fun s : ℂ => cexp (2 * π * I * t * s)) w := by fun_prop
    exact (DifferentiableAt.comp w hd hinner).const_mul _
  refine hcomp.congr_of_eventuallyEq ?_
  have hopen : {s : ℂ | 0 < s.im} ∈ 𝓝 w :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hw
  filter_upwards [hopen] with s hs
  rw [lamSum_eq G (jj ℓ) (A := A) hlam hN hsf ht hA hAb s.re hs, hqeq]
  rfl

/-- **`AADRaisedModularity` for `t = 1`.** -/
theorem raised_of_one (h5 : 5 ≤ ℓ) {a : PowerSeries ℤ} (ha : a ∈ intLattice ℓ)
    (ht : 24 ∣ 1 + jj ℓ) [NeZero (1 : ℕ)] [NeZero (6 * 1 : ℕ)] :
    ∃ g : ModularForm (Gamma0 (6 * 1) : Subgroup (GL (Fin 2) ℝ)) ((2 * halfWt ℓ : ℕ) : ℤ),
      qExpansion 1 g = PowerSeries.expand 1 (NeZero.ne 1)
        (PowerSeries.map (Int.castRingHom ℂ) (liftSeries ℓ 1 (coordOf ℓ a))) := by
  obtain ⟨G, hG⟩ := ha
  obtain ⟨hj, ht2, ht3, hNj, hjw, hk, hlam, hneg⟩ := arithData (ℓ := ℓ) h5 ht
  have hl23 : 23 ≤ ℓ := by
    have : jj ℓ ≤ ℓ := Nat.mod_le _ _
    omega
  obtain ⟨μ, hμ⟩ : ∃ μ, halfWt ℓ = μ + 1 := ⟨halfWt ℓ - 1, by omega⟩
  have hμ0 : μ ≠ 0 := by
    unfold halfWt at hμ
    omega
  refine raised_of_covariant h5 G hG squarefree_one ht fun γ E hE w hw => ?_
  have hT : ∀ t : ℂ, 0 < t.im → DifferentiableAt ℂ
      (fun t : ℂ => lamSum G (jj ℓ) (N := 1) (jN 1) (μ + 1) t.re t.im) t := by
    intro t ht'
    have := lamSum_differentiableAt h5 G hG one_pos squarefree_one ht ht'
    rwa [hμ] at this
  rw [hμ] at hk hneg ⊢
  have h := defect_one G (jj ℓ) μ hμ0 hj hNj ht hjw hk hneg hT γ hE hw
  unfold defectT at h
  exact sub_eq_zero.mp h

/-- **`AADRaisedModularity` holds.** -/
theorem aadRaisedModularity (h5 : 5 ≤ ℓ) : AADRaisedModularity ℓ := by
  intro a ha t hsf ht _ _
  by_cases ht1 : t = 1
  · subst ht1
    exact raised_of_one h5 ha ht
  · exact raised_of_ne_one h5 ha hsf ht ht1

/-- **Modularity of the Shimura lifts** (Ahlgren–Andersen–Dicks, Theorem 1.1). -/
theorem aadModularity (h5 : 5 ≤ ℓ) : AADModularity ℓ :=
  aadModularity_of_raised (aadRaisedModularity h5)

/-- **Theorem A, unconditionally.** -/
theorem theoremA_unconditional (h13 : 13 ≤ ℓ) {a : PowerSeries ℤ} (ha : a ∈ intLattice ℓ)
    (hU : ∀ m, (ℓ : ℤ) ∣ (coordOf ℓ a).coeff (ℓ ^ 2 * m - jj ℓ * δ ℓ)) :
    ∀ m, (ℓ : ℤ) ∣ a.coeff m :=
  theoremA_of_modularity h13 (aadModularity (by omega)) ha hU

/-- **The injectivity of `X`, unconditionally.** -/
theorem X_injective_unconditional (h13 : 13 ≤ ℓ) {a : PowerSeries ℤ} (ha : a ∈ intLattice ℓ)
    (hX : Ψ ℓ (U ℓ (Φ ℓ * U ℓ (Dz ^ tt ℓ * a))) = 0) : Ψ ℓ a = 0 :=
  X_injective_of_modularity h13 (aadModularity (by omega)) ha hX

end

end RamanujanTau.ThetaLift
