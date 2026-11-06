/-
# M2.1: a concrete smooth admissible window `φ_T(t) = Φ(t/T)`

`Φ` is a `C^∞` bump (`ContDiffBump` at `7/4`, radii `3/4`, `1`): `0 ≤ Φ ≤ 1`, `Φ = 1` on
`[1, 5/2]`, `Φ, Φ', Φ''` vanish outside `[3/4, 11/4]` and are bounded.

* `admissible_phiT`: `φ_T` is admissible on `[T/2, 3T]` (`SelbergKey.Admissible`);
* `hasDerivAt_phiT`, `hasDerivAt_phiT1`: `φ_T' = Φ'(t/T)/T`, `φ_T'' = Φ''(t/T)/T²`;
* `phiT_zero_outside`: all three vanish unless `t/T ∈ [3/4, 11/4]`.
Level 1.
-/
import RamanujanTau.SelbergKey.Reduce

set_option autoImplicit false

namespace RamanujanTau.SelbergKey4

open Set Filter Topology

/-- The bump at `7/4` with radii `3/4 < 1`. -/
noncomputable def bump0 : ContDiffBump (7 / 4 : ℝ) := ⟨3 / 4, 1, by norm_num, by norm_num⟩

/-- The profile `Φ`. -/
noncomputable def Phi (s : ℝ) : ℝ := bump0 s

noncomputable def Phi1 : ℝ → ℝ := deriv Phi
noncomputable def Phi2 : ℝ → ℝ := deriv Phi1

lemma contDiff_Phi (n : ℕ∞) : ContDiff ℝ n Phi := bump0.contDiff

lemma Phi_nonneg (s : ℝ) : 0 ≤ Phi s := bump0.nonneg

lemma Phi_le_one (s : ℝ) : Phi s ≤ 1 := bump0.le_one

lemma Phi_eq_one {s : ℝ} (h1 : 1 ≤ s) (h2 : s ≤ 5 / 2) : Phi s = 1 := by
  apply bump0.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
  show -(3/4 : ℝ) ≤ s - 7 / 4 ∧ s - 7 / 4 ≤ 3 / 4
  constructor <;> linarith

lemma tsupport_Phi : tsupport Phi ⊆ Icc (3 / 4) (11 / 4) := by
  have : tsupport Phi = Metric.closedBall (7 / 4 : ℝ) 1 := bump0.tsupport_eq
  rw [this]
  intro s hs
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hs
  constructor <;> linarith [hs.1, hs.2]

lemma hasDerivAt_Phi (s : ℝ) : HasDerivAt Phi (Phi1 s) s :=
  ((contDiff_Phi 1).differentiable (by norm_num) s).hasDerivAt

lemma contDiff_Phi1 : ContDiff ℝ 1 Phi1 := by
  have h : ContDiff ℝ (1 + 1) Phi := bump0.contDiff
  exact (contDiff_succ_iff_deriv.1 h).2.2

lemma hasDerivAt_Phi1 (s : ℝ) : HasDerivAt Phi1 (Phi2 s) s :=
  (contDiff_Phi1.differentiable (by norm_num) s).hasDerivAt

lemma continuous_Phi2 : Continuous Phi2 := contDiff_Phi1.continuous_deriv le_rfl

lemma Phi_zero_outside {s : ℝ} (hs : s ∉ Icc (3 / 4 : ℝ) (11 / 4)) :
    Phi s = 0 ∧ Phi1 s = 0 ∧ Phi2 s = 0 := by
  have h0 : s ∉ tsupport Phi := fun h => hs (tsupport_Phi h)
  have h1 : s ∉ tsupport Phi1 := fun h => h0 (tsupport_deriv_subset (𝕜 := ℝ) h)
  have h2 : s ∉ tsupport Phi2 := fun h => h1 (tsupport_deriv_subset (𝕜 := ℝ) h)
  exact ⟨image_eq_zero_of_notMem_tsupport h0, image_eq_zero_of_notMem_tsupport h1,
    image_eq_zero_of_notMem_tsupport h2⟩

lemma Phi_bounds : ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℝ, |Phi s| ≤ M ∧ |Phi1 s| ≤ M ∧ |Phi2 s| ≤ M := by
  have hc0 : HasCompactSupport Phi := bump0.hasCompactSupport
  have hc1 : HasCompactSupport Phi1 := hc0.deriv
  have hc2 : HasCompactSupport Phi2 := hc1.deriv
  obtain ⟨M0, hM0⟩ := (contDiff_Phi 0).continuous.bounded_above_of_compact_support hc0
  obtain ⟨M1, hM1⟩ := contDiff_Phi1.continuous.bounded_above_of_compact_support hc1
  obtain ⟨M2, hM2⟩ := continuous_Phi2.bounded_above_of_compact_support hc2
  refine ⟨|M0| + |M1| + |M2|, by positivity, fun s => ⟨?_, ?_, ?_⟩⟩
  · have := hM0 s; rw [Real.norm_eq_abs] at this
    linarith [le_abs_self M0, abs_nonneg M1, abs_nonneg M2]
  · have := hM1 s; rw [Real.norm_eq_abs] at this
    linarith [le_abs_self M1, abs_nonneg M0, abs_nonneg M2]
  · have := hM2 s; rw [Real.norm_eq_abs] at this
    linarith [le_abs_self M2, abs_nonneg M1, abs_nonneg M0]

/-- **The window** `φ_T(t) = Φ(t/T)`. -/
noncomputable def phiT (T t : ℝ) : ℝ := Phi (t / T)

theorem admissible_phiT {T : ℝ} (hT : 0 < T) :
    SelbergKey.Admissible T (T / 2) (3 * T) (phiT T) := by
  refine ⟨(contDiff_Phi 0).continuous.comp (continuous_id.div_const T), fun t => Phi_nonneg _,
    fun t ht => ?_, by linarith, by linarith⟩
  have h1 : 1 ≤ t / T := by rw [le_div_iff₀ hT]; linarith [ht.1]
  have h2 : t / T ≤ 5 / 2 := by rw [div_le_iff₀ hT]; linarith [ht.2]
  exact (Phi_eq_one h1 h2).ge

lemma hasDerivAt_phiT {T : ℝ} (t : ℝ) : HasDerivAt (phiT T) (Phi1 (t / T) / T) t := by
  have := (hasDerivAt_Phi (t / T)).comp t ((hasDerivAt_id t).div_const T)
  simpa [phiT, div_eq_mul_inv, mul_comm] using this

lemma hasDerivAt_phiT1 {T : ℝ} (t : ℝ) :
    HasDerivAt (fun t => Phi1 (t / T) / T) (Phi2 (t / T) / T ^ 2) t := by
  have := ((hasDerivAt_Phi1 (t / T)).comp t ((hasDerivAt_id t).div_const T)).div_const T
  convert this using 1
  field_simp

lemma phiT_zero_outside {T t : ℝ} (hT : 0 < T) (ht : t ∉ Icc (3 / 4 * T) (11 / 4 * T)) :
    Phi (t / T) = 0 ∧ Phi1 (t / T) = 0 ∧ Phi2 (t / T) = 0 := by
  apply Phi_zero_outside
  intro h
  apply ht
  constructor
  · have := h.1; rw [le_div_iff₀ hT] at this; linarith
  · have := h.2; rw [div_le_iff₀ hT] at this; linarith

end RamanujanTau.SelbergKey4
