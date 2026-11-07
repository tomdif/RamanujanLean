/-
# Riemann's formula for `Λ₀` and the Mellin derivatives (milestone M2, part 1)

Mathlib: `completedRiemannZeta₀ s = Λ₀^{P}(s/2)/2` with `P = hurwitzEvenFEPair 0` (`f = θ = evenKernel 0`,
`f₀ = g₀ = 1`, `k = 1/2`, `ε = 1`), `Λ₀^{P} = mellin f_modif`,
`f_modif = 1_{(1,∞)}(θ − 1) + 1_{(0,1)}(θ − x^{−1/2})`.

* `mellin_fmodif_split` : `Λ₀^{P}(w) = M(w) + M(1/2 − w)` with `M = mellin A`, `A = 1_{(1,∞)}(θ − 1)` (the
  `(0,1)` piece is turned into the `(1,∞)` piece by `t ↦ 1/t` and `θ(1/t) = t^{1/2} θ(t)`).
* `completedRiemannZeta₀_eq` : `Λ₀(s) = (M(s/2) + M((1−s)/2))/2`  — Riemann's formula (GORZ (11)).
* `hasDerivAt_mellin_Am` : `d/dw mellin(log^m · A)(w) = mellin(log^{m+1} · A)(w)` for every `w ∈ ℂ`.
-/
import RamanujanTau.GORZXi.XiMain

set_option autoImplicit false

namespace GORZXi

open Filter Topology Set MeasureTheory Asymptotics HurwitzZeta

/-- `A(t) = 1_{t>1} (θ(t) − 1)`. -/
noncomputable def Aθ : ℝ → ℂ := (Ioi 1).indicator (fun x => ((evenKernel 0 x : ℝ) : ℂ) - 1)

/-- `B(t) = 1_{0<t<1} (θ(t) − t^{−1/2})`. -/
noncomputable def Bθ : ℝ → ℂ :=
  (Ioo 0 1).indicator (fun x => ((evenKernel 0 x : ℝ) : ℂ) - ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))

lemma fmodif_eq : (hurwitzEvenFEPair 0).f_modif = Aθ + Bθ := by
  funext x
  simp [WeakFEPair.f_modif, hurwitzEvenFEPair, Aθ, Bθ]

lemma conv_fmodif (w : ℂ) : MellinConvergent (hurwitzEvenFEPair 0).f_modif w :=
  ((hurwitzEvenFEPair 0).toStrongFEPair.hasMellin w).1

lemma Aθ_eq_ind : Aθ = (Ioi 1).indicator (hurwitzEvenFEPair 0).f_modif := by
  funext x
  rw [fmodif_eq]
  by_cases hx : x ∈ Ioi 1
  · have : x ∉ Ioo (0 : ℝ) 1 := fun h => by simp only [mem_Ioi, mem_Ioo] at hx h; linarith
    simp [indicator_of_mem hx, Aθ, Bθ, indicator_of_notMem this]
  · simp [indicator_of_notMem hx, Aθ]

lemma Bθ_eq_ind : Bθ = (Ioo 0 1).indicator (hurwitzEvenFEPair 0).f_modif := by
  funext x
  rw [fmodif_eq]
  by_cases hx : x ∈ Ioo (0 : ℝ) 1
  · have : x ∉ Ioi (1 : ℝ) := fun h => by simp only [mem_Ioi, mem_Ioo] at hx h; linarith
    simp [indicator_of_mem hx, Aθ, Bθ, indicator_of_notMem this]
  · simp [indicator_of_notMem hx, Bθ]

lemma conv_ind {S : Set ℝ} (hS : MeasurableSet S) (w : ℂ) :
    MellinConvergent (S.indicator (hurwitzEvenFEPair 0).f_modif) w := by
  have h := (conv_fmodif w).indicator hS
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  by_cases ht : t ∈ S
  · simp [indicator_of_mem ht]
  · simp [indicator_of_notMem ht]

lemma convA (w : ℂ) : MellinConvergent Aθ w := by rw [Aθ_eq_ind]; exact conv_ind measurableSet_Ioi w
lemma convB (w : ℂ) : MellinConvergent Bθ w := by rw [Bθ_eq_ind]; exact conv_ind measurableSet_Ioo w

lemma Bθ_inv {t : ℝ} (ht : 0 < t) : Bθ t⁻¹ = (t : ℂ) ^ ((1 / 2 : ℝ) : ℂ) • Aθ t := by
  rcases le_or_gt t 1 with h1 | h1
  · have hA : t ∉ Ioi (1 : ℝ) := by simpa using h1
    have hB : t⁻¹ ∉ Ioo (0 : ℝ) 1 := by
      simp only [mem_Ioo, not_and, not_lt]; intro _; exact one_le_inv₀ ht |>.mpr h1
    simp [Aθ, Bθ, indicator_of_notMem hA, indicator_of_notMem hB]
  · have hA : t ∈ Ioi (1 : ℝ) := h1
    have hB : t⁻¹ ∈ Ioo (0 : ℝ) 1 := ⟨inv_pos.mpr ht, inv_lt_one_of_one_lt₀ h1⟩
    simp only [Aθ, Bθ, indicator_of_mem hA, indicator_of_mem hB]
    have hfe := evenKernel_functional_equation 0 t⁻¹
    rw [← evenKernel_eq_cosKernel_of_zero, show (1 : ℝ) / t⁻¹ = t by rw [one_div, inv_inv],
      Real.inv_rpow ht.le, div_inv_eq_mul, one_mul] at hfe
    rw [hfe, show (t⁻¹) ^ (-(1 / 2 : ℝ)) = t ^ (1 / 2 : ℝ) by
      rw [Real.rpow_neg (inv_nonneg.mpr ht.le), Real.inv_rpow ht.le, inv_inv],
      smul_eq_mul, ← Complex.ofReal_cpow ht.le]
    push_cast
    ring

/-- `Λ₀^{P}(w) = M(w) + M(1/2 − w)`. -/
theorem mellin_fmodif_split (w : ℂ) :
    (hurwitzEvenFEPair 0).Λ₀ w = mellin Aθ w + mellin Aθ (1 / 2 - w) := by
  rw [WeakFEPair.Λ₀, fmodif_eq]
  have hadd := (hasMellin_add (convA w) (convB w)).2
  rw [show (fun t => Aθ t + Bθ t) = Aθ + Bθ from rfl] at hadd
  rw [hadd]
  congr 1
  have h1 : mellin Bθ w = mellin (fun t => Bθ t⁻¹) (-w) := by
    have := mellin_comp_inv (fun t => Bθ t⁻¹) w
    simp only [inv_inv] at this
    exact this
  rw [h1]
  have h2 : mellin (fun t => Bθ t⁻¹) (-w) = mellin (fun t => (t : ℂ) ^ ((1 / 2 : ℝ) : ℂ) • Aθ t) (-w) := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only
    rw [Bθ_inv ht]
  rw [h2, mellin_cpow_smul]
  congr 1
  push_cast; ring

/-- **Riemann's formula** `Λ₀(s) = (M(s/2) + M((1−s)/2))/2`, `M(w) = ∫_1^∞ t^{w−1}(θ(t) − 1) dt`. -/
theorem completedRiemannZeta₀_eq (s : ℂ) :
    completedRiemannZeta₀ s = (mellin Aθ (s / 2) + mellin Aθ (1 / 2 - s / 2)) / 2 := by
  rw [completedRiemannZeta₀, completedHurwitzZetaEven₀, mellin_fmodif_split]

/-! ## Mellin derivatives -/

/-- `A_m(t) = (log t)^m A(t)`. -/
noncomputable def Am (m : ℕ) (t : ℝ) : ℂ := (Real.log t ^ m : ℝ) • Aθ t

lemma Am_zero : Am 0 = Aθ := by funext t; simp [Am]

lemma Am_succ (m : ℕ) : (fun t => Real.log t • Am m t) = Am (m + 1) := by
  funext t; simp only [Am, smul_smul, pow_succ]; ring_nf

lemma Am_eq_ind (m : ℕ) : Am m = (Ioi 1).indicator
    (fun t => (Real.log t ^ m : ℝ) • (((evenKernel 0 t : ℝ) : ℂ) - 1)) := by
  funext t
  by_cases ht : t ∈ Ioi (1 : ℝ)
  · simp [Am, Aθ, indicator_of_mem ht]
  · simp [Am, Aθ, indicator_of_notMem ht]

lemma Am_locInt (m : ℕ) : LocallyIntegrableOn (Am m) (Ioi 0) := by
  have hc : ContinuousOn (fun t : ℝ => (Real.log t ^ m : ℝ) • (((evenKernel 0 t : ℝ) : ℂ) - 1)) (Ioi 0) := by
    refine ContinuousOn.smul ?_ ?_
    · exact (Real.continuousOn_log.mono fun x hx => ne_of_gt hx).pow m
    · exact (Complex.continuous_ofReal.comp_continuousOn (continuousOn_evenKernel 0)).sub continuousOn_const
  have hl := hc.locallyIntegrableOn (μ := volume) measurableSet_Ioi
  rw [Am_eq_ind]
  intro x hx
  obtain ⟨s, hs, hs'⟩ := hl x hx
  exact ⟨s, hs, hs'.indicator measurableSet_Ioi⟩

lemma Am_top (m : ℕ) (a : ℝ) : Am m =O[atTop] (· ^ (-a)) := by
  have h1 := (hurwitzEvenFEPair 0).hf_top (-a - 1)
  have h2 : (fun t : ℝ => Real.log t ^ m) =O[atTop] (fun t : ℝ => t ^ (1 : ℝ)) :=
    Real.isLittleO_pow_log_id_atTop.isBigO.congr_right fun x => (Real.rpow_one x).symm
  have h3 := h2.smul h1
  refine h3.congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop 1] with t ht
    simp [Am, Aθ, indicator_of_mem (show t ∈ Ioi (1 : ℝ) from ht), hurwitzEvenFEPair]
  · filter_upwards [eventually_gt_atTop 0] with t ht
    simp only [smul_eq_mul]
    rw [← Real.rpow_add ht]; ring_nf

lemma Am_bot (m : ℕ) (b : ℝ) : Am m =O[𝓝[>] 0] (· ^ (-b)) := by
  refine (isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
  have : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 := nhdsWithin_le_nhds (eventually_lt_nhds one_pos)
  filter_upwards [this] with t ht
  have : t ∉ Ioi (1 : ℝ) := by simp only [mem_Ioi, not_lt]; exact ht.le
  simp [Am, Aθ, indicator_of_notMem this]

theorem hasDerivAt_mellin_Am (m : ℕ) (w : ℂ) : HasDerivAt (mellin (Am m)) (mellin (Am (m + 1)) w) w := by
  have h := mellin_hasDerivAt_of_isBigO_rpow (a := w.re + 1) (b := w.re - 1) (Am_locInt m)
    (Am_top m _) (by linarith) (Am_bot m _) (by linarith)
  rw [Am_succ] at h
  exact h.2

end GORZXi
