/-
# The completed Rankin–Selberg integral: continuation, functional equation, boundedness

`rsFE : WeakFEPair ℂ` (Mathlib's abstract Mellin functional-equation package) for
`Φ(t) = ∫_𝓕 G Θ_t dμ`, `Φ(1/t) = tΦ(t)`, `Φ − ‖Δ‖²` rapidly decreasing. It gives an entire
`Λ₀ = rsFE.Λ₀` with `Λ₀(1−s) = Λ₀(s)`, bounded on vertical strips, and

    mellin (Φ − ‖Δ‖²) s = Λ₀(s) + ‖Δ‖² (1/(s−1) − 1/s)       (Re s > 1).

`rsData_of_unfold`: the only remaining input is the unfolding identity `RSUnfold`
(`mellin (Φ − ‖Δ‖²) = γ(s) ζ(2s) ∑ τ(n)² n^{−s−11}`, `Re s > 2`). Hence
`rankinSelberg_power_saving_of_unfold`.
-/
import RamanujanTau.RankinError.ThetaInt
import RamanujanTau.RankinError.Tau

set_option autoImplicit false

namespace RamanujanTau.RankinError

open Real Filter Topology MeasureTheory Set Asymptotics
open RamanujanTau.RankinSelberg RamanujanTau.EisensteinReal RamanujanTau.EisensteinReal.Horo

lemma locallyIntegrableOn_Phi : LocallyIntegrableOn (fun t => (Phi t : ℂ)) (Ioi 0) := by
  refine (locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).2 fun K hK hKc => ?_
  exact ((Phi_antitoneOn.mono hK).integrableOn_isCompact hKc).ofReal

lemma Phi_top (r : ℝ) : (fun t => (Phi t : ℂ) - (petNormSq : ℂ)) =O[atTop] (· ^ r) := by
  obtain ⟨R, hR⟩ := exists_nat_ge (-r)
  obtain ⟨C, hC⟩ := Phi_sub_le R
  refine IsBigO.of_bound (|C| * 2 ^ (R : ℝ)) ?_
  filter_upwards [eventually_ge_atTop (2:ℝ)] with t ht
  have ht0 : 0 < t := by linarith
  obtain ⟨h0, h1⟩ := hC t (by linarith)
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
  have hR0 : -(R : ℝ) ≤ 0 := by simp
  have e1 : (t - 1) ^ (-(R : ℝ)) ≤ (t / 2) ^ (-(R : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) hR0
  have e2 : (t / 2) ^ (-(R : ℝ)) = 2 ^ (R : ℝ) * t ^ (-(R : ℝ)) := by
    rw [Real.div_rpow ht0.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    field_simp
  have e3 : t ^ (-(R : ℝ)) ≤ t ^ r := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  calc Phi t - petNormSq ≤ C * (t - 1) ^ (-(R : ℝ)) := h1
    _ ≤ |C| * (t - 1) ^ (-(R : ℝ)) := mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (by linarith) _)
    _ ≤ |C| * (2 ^ (R : ℝ) * t ^ (-(R : ℝ))) := by rw [← e2]; gcongr
    _ ≤ |C| * (2 ^ (R : ℝ) * t ^ r) := by gcongr
    _ = |C| * 2 ^ (R : ℝ) * t ^ r := by ring

/-- The weak functional-equation pair `(Φ, Φ)`, weight `1`, root number `1`, constant `‖Δ‖²`. -/
noncomputable def rsFE : WeakFEPair ℂ where
  f := fun t => (Phi t : ℂ)
  g := fun t => (Phi t : ℂ)
  k := 1
  ε := 1
  f₀ := (petNormSq : ℂ)
  g₀ := (petNormSq : ℂ)
  hf_int := locallyIntegrableOn_Phi
  hg_int := locallyIntegrableOn_Phi
  hk := one_pos
  hε := one_ne_zero
  h_feq := fun x hx => by
    simp only [Real.rpow_one, one_mul]
    rw [Phi_inv hx]; push_cast; ring
  hf_top := Phi_top
  hg_top := Phi_top

lemma rsFE_symm_Λ₀ : rsFE.symm.Λ₀ = rsFE.Λ₀ := by
  funext s
  simp only [WeakFEPair.Λ₀, WeakFEPair.f_modif, WeakFEPair.symm, rsFE, inv_one]

lemma rpow_le_add {t a σ b : ℝ} (ht : 0 < t) (ha : a ≤ σ) (hb : σ ≤ b) :
    t ^ (σ - 1) ≤ t ^ (a - 1) + t ^ (b - 1) := by
  rcases le_or_gt t 1 with h | h
  · have := Real.rpow_le_rpow_of_exponent_ge ht h (show a - 1 ≤ σ - 1 by linarith)
    linarith [Real.rpow_pos_of_pos ht (b - 1)]
  · have := Real.rpow_le_rpow_of_exponent_le h.le (show σ - 1 ≤ b - 1 by linarith)
    linarith [Real.rpow_pos_of_pos ht (a - 1)]

/-- `Λ₀` is bounded on every vertical strip. -/
lemma rsFE_Λ₀_bdd (a b : ℝ) : ∃ L : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖rsFE.Λ₀ s‖ ≤ L := by
  set f := rsFE.f_modif
  have hconv : ∀ s : ℂ, MellinConvergent f s := fun s => (rsFE.toStrongFEPair.hasMellin s).1
  set L := (∫ t in Ioi (0:ℝ), ‖(t : ℂ) ^ ((a : ℂ) - 1) • f t‖) +
    ∫ t in Ioi (0:ℝ), ‖(t : ℂ) ^ ((b : ℂ) - 1) • f t‖ with hL
  refine ⟨L, fun s h1 h2 => ?_⟩
  have hΛ : rsFE.Λ₀ s = mellin f s := rfl
  rw [hΛ, mellin]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hia := (hconv a).norm
  have hib := (hconv b).norm
  rw [hL, ← integral_add hia hib]
  refine setIntegral_mono_on (hconv s).norm (hia.add hib) measurableSet_Ioi fun t ht => ?_
  simp only [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (rpow_le_add ht h1 h2) (norm_nonneg _)

/-- **The remaining input: the Rankin–Selberg unfolding identity.** -/
def RSUnfold : Prop :=
  ∀ s : ℂ, 2 < s.re → mellin (fun t => (Phi t : ℂ) - (petNormSq : ℂ)) s =
    gam s * riemannZeta (2 * s) * LSeries (fun n => (aTau n : ℂ)) s

/-- The continuation, functional equation and boundedness are now proved; only the unfolding
identity is assumed. -/
noncomputable def rsData_of_unfold (h : RSUnfold) : RSData aTau petNormSq where
  Λ₀ := rsFE.Λ₀
  diff := rsFE.differentiable_Λ₀
  L₀ := (rsFE_Λ₀_bdd (-3 / 2) (5 / 2)).choose
  bdd := (rsFE_Λ₀_bdd (-3 / 2) (5 / 2)).choose_spec
  fe := fun s => by
    have := rsFE.functional_equation₀ s
    rw [rsFE_symm_Λ₀] at this
    simpa [rsFE] using this
  unfold := fun s hs => by
    rw [← h s hs]
    have hm := (rsFE.hasMellin (s := s) (by simp [rsFE]; linarith)).2
    have hm' : mellin (fun t => (Phi t : ℂ) - (petNormSq : ℂ)) s = rsFE.Λ s := hm
    rw [hm', WeakFEPair.Λ]
    change rsFE.Λ₀ s - (1 / s) • (petNormSq : ℂ) - ((1:ℂ) / (((1:ℝ):ℂ) - s)) • (petNormSq : ℂ) = _
    simp only [smul_eq_mul, Complex.ofReal_one]
    have hs0 : s ≠ 0 := by intro h0; rw [h0] at hs; simp at hs; linarith
    have hs1 : (1:ℂ) - s ≠ 0 := by
      intro h1; have := congrArg Complex.re h1; simp at this; linarith
    have hs1' : s - 1 ≠ 0 := by
      intro h1; have := congrArg Complex.re h1; simp at this; linarith
    field_simp
    ring

/-- **Power-saving Rankin–Selberg, conditional only on the unfolding identity.** -/
theorem rankinSelberg_power_saving_of_unfold (h : RSUnfold) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 -
          3 / π * (4 * π) ^ 12 * petNormSq / (Nat.factorial 11 : ℝ) * N| ≤
        C * (N : ℝ) ^ (1 - 1 / 2 ^ 22 : ℝ) :=
  rankinSelberg_power_saving_of_RSData (rsData_of_unfold h)

end RamanujanTau.RankinError
