/-
# An abstract Rankin–Selberg test function: `HoroFn` + Parseval + cusp decay

`RSFn` extends `RankinSelbergGeneral.HoroFn` (continuous, `≥ 0`, bounded, `SL₂(ℤ)`-invariant `G`)
by the two further properties used by the unfolding argument of `RankinError/`:

* `parseval`: `∫₀¹ G(x+iy) dx = ∑ₙ cₙ y^{m+1} e^{−4πny}` with `cₙ ≥ 0`, `c₀ = 0`
  (for `G = |f|²y^k`: `cₙ = |a_f(n)|²`, `m = k − 1`);
* `exp_decay`: `G(z) ≤ K e^{−c Im z}` for `Im z ≥ ½`.

Consequences proved here: `cₙ ≤ K n^{m+1}` (from Parseval and boundedness), hence
`aₙ = cₙ/n^m ≤ K n` and `∑ aₙ n^{−5/2} < ∞`; the strip side of the unfolding
`∫₀^∞ I(y) y^{s−2} dy = ∑ cₙ Γ(s+m)(4πn)^{−s−m}` (`lintegral_mellin_horocycleG`, in `[0,∞]`).
-/
import RamanujanTau.RankinSelbergGeneral.GIdent
import RamanujanTau.RankinErrorGeneral.Saving
import RamanujanTau.RankinError.PowerSaving84

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanTau.RankinErrorGeneral

open Real Filter Topology MeasureTheory Set
open RamanujanTau.RankinSelberg hiding G G_smul continuous_G G_pos
open RamanujanTau.RankinSelbergGeneral RamanujanTau.RankinSelbergGeneral.Horo
open HoroFn
open UpperHalfPlane hiding I

/-- A `HoroFn` with a Parseval expansion of weight `m + 1` and exponential decay at the cusp. -/
class RSFn extends HoroFn where
  m : ℕ
  cf : ℕ → ℝ
  cf_nonneg : ∀ n, 0 ≤ cf n
  cf_zero : cf 0 = 0
  parseval : ∀ {y : ℝ} (hy : 0 < y), HasSum
    (fun n : ℕ => cf n * (y ^ (m + 1) * Real.exp (-(4 * π * n) * y)))
    (∫ x in (0 : ℝ)..1, G (hp hy x))
  exp_decay : ∃ K c : ℝ, 0 ≤ K ∧ 0 < c ∧ ∀ z : ℍ, 1 / 2 ≤ z.im → G z ≤ K * Real.exp (-c * z.im)

open RSFn

variable [RSFn]

/-- The normalized coefficients `aₙ = cₙ / n^m`. -/
noncomputable def aF (n : ℕ) : ℝ := cf n / (n : ℝ) ^ m

lemma aF_nonneg (n : ℕ) : 0 ≤ aF n := by
  unfold aF; have := cf_nonneg n; positivity

lemma aF_zero : aF 0 = 0 := by simp [aF, cf_zero]

lemma Aint_le {M : ℝ} (hM : ∀ z : ℍ, G z ≤ M) {y : ℝ} (hy : 0 < y) :
    ∫ x in (0 : ℝ)..1, G (hp hy x) ≤ M := by
  have h := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
    ((continuous_G_hp hy).intervalIntegrable 0 1) (continuous_const.intervalIntegrable 0 1)
    (fun x _ => hM (hp hy x))
  simpa using h

/-- `cₙ ≤ K n^{m+1}`. -/
lemma exists_cf_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, cf n ≤ K * (n : ℝ) ^ (m + 1) := by
  obtain ⟨M, hM0, hM⟩ := exists_G_le
  refine ⟨M * Real.exp (4 * π), by positivity, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [cf_zero]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set y : ℝ := 1 / n with hy
  have hy0 : 0 < y := by positivity
  have hs := parseval hy0
  have hle : cf n * (y ^ (m + 1) * Real.exp (-(4 * π * n) * y)) ≤ M :=
    (hs.summable.le_tsum n (fun j _ => mul_nonneg (cf_nonneg j) (by positivity))).trans
      (hs.tsum_eq ▸ Aint_le hM hy0)
  have e1 : Real.exp (-(4 * π * n) * y) = Real.exp (-(4 * π)) := by
    congr 1; rw [hy]; field_simp
  have e2 : y ^ (m + 1) * (n : ℝ) ^ (m + 1) = 1 := by
    rw [← mul_pow, hy, one_div_mul_cancel hn0.ne', one_pow]
  rw [e1] at hle
  have hE : Real.exp (-(4 * π)) * Real.exp (4 * π) = 1 := by rw [← Real.exp_add]; simp
  calc cf n = cf n * (y ^ (m + 1) * Real.exp (-(4 * π))) * (Real.exp (4 * π) * (n : ℝ) ^ (m + 1)) := by
        have : cf n * (y ^ (m + 1) * Real.exp (-(4 * π))) * (Real.exp (4 * π) * (n : ℝ) ^ (m + 1))
            = cf n * (y ^ (m + 1) * (n : ℝ) ^ (m + 1)) * (Real.exp (-(4 * π)) * Real.exp (4 * π)) := by
          ring
        rw [this, e2, hE]; ring
    _ ≤ M * (Real.exp (4 * π) * (n : ℝ) ^ (m + 1)) :=
        mul_le_mul_of_nonneg_right hle (by positivity)
    _ = _ := by ring

lemma exists_aF_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, aF n ≤ K * n := by
  obtain ⟨K, hK0, hK⟩ := exists_cf_le
  refine ⟨K, hK0, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [aF_zero]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold aF
  rw [div_le_iff₀ (by positivity)]
  calc cf n ≤ K * (n : ℝ) ^ (m + 1) := hK n
    _ = K * n * (n : ℝ) ^ m := by ring

lemma summable_aF : Summable fun n : ℕ => aF n * (n : ℝ) ^ (-(5 / 2 : ℝ)) := by
  obtain ⟨K, hK0, hK⟩ := exists_aF_le
  have hs : Summable fun n : ℕ => K * (n : ℝ) ^ (-(3 / 2 : ℝ)) :=
    (Real.summable_nat_rpow.2 (by norm_num)).mul_left K
  refine hs.of_nonneg_of_le (fun n => mul_nonneg (aF_nonneg n) (by positivity)) (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [aF_zero]
  · have hn : (0:ℝ) < n := by exact_mod_cast h
    calc aF n * (n : ℝ) ^ (-(5 / 2 : ℝ)) ≤ K * n * (n : ℝ) ^ (-(5 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (hK n) (by positivity)
      _ = K * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
          rw [mul_assoc]; congr 1
          rw [show -(3 / 2 : ℝ) = 1 + -(5 / 2) by norm_num, Real.rpow_add hn, Real.rpow_one]

/-! ### The strip side of the unfolding -/

/-- The `n`-th term `cₙ y^{s+m−1} e^{−4πny}`. -/
noncomputable def mtermG (s : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  cf n * (y ^ (s + m - 1) * Real.exp (-(4 * π * n) * y))

lemma mtermG_nonneg (s : ℝ) (n : ℕ) {y : ℝ} (hy : 0 < y) : 0 ≤ mtermG s n y := by
  unfold mtermG
  exact mul_nonneg (cf_nonneg n) (mul_nonneg (Real.rpow_nonneg hy.le _) (Real.exp_pos _).le)

lemma hasSum_mtermG (s : ℝ) {y : ℝ} (hy : 0 < y) :
    HasSum (fun n => mtermG s n y) (Aint y * y ^ (s - 2)) := by
  have h := (parseval hy).mul_right (y ^ (s - 2))
  have e2 : y ^ (s + m - 1) = y ^ (m + 1) * y ^ (s - 2) := by
    rw [show s + m - 1 = (((m + 1 : ℕ) : ℝ)) + (s - 2) by push_cast; ring, Real.rpow_add hy,
      Real.rpow_natCast]
  unfold Aint
  rw [dif_pos hy]
  convert h using 1
  funext n; unfold mtermG; rw [e2]; ring

lemma integral_mtermG {s : ℝ} (hs : -(m : ℝ) < s) {n : ℕ} (hn : 1 ≤ n) :
    ∫ y in Ioi (0 : ℝ), mtermG s n y = cf n * Real.Gamma (s + m) / (4 * π * n) ^ (s + m) := by
  have hb : 0 < 4 * π * (n : ℝ) := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  unfold mtermG
  rw [integral_const_mul]
  have e : ∀ y : ℝ, y ^ (s + m - 1) * Real.exp (-(4 * π * n) * y) =
      y ^ ((s + m) - 1) * Real.exp (-((4 * π * n) * y)) := by
    intro y; rw [neg_mul]
  simp_rw [e]
  rw [integral_rpow_mul_exp_neg_mul_Ioi (by linarith) hb, Real.div_rpow zero_le_one hb.le,
    Real.one_rpow]
  ring

lemma integrableOn_mtermG {s : ℝ} (hs : -(m : ℝ) < s) {n : ℕ} (hn : 1 ≤ n) :
    IntegrableOn (mtermG s n) (Ioi 0) := by
  have hb : 0 < 4 * π * (n : ℝ) := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have h := (integrableOn_rpow_mul_exp_neg_mul_rpow (s := s + m - 1) (p := 1) (by linarith) le_rfl
    hb).const_mul (cf n)
  simp only [Real.rpow_one] at h
  exact h

/-- **Strip side of the unfolding** (in `[0, ∞]`, real `s > −m`):
`∫₀^∞ I(y) y^{s−2} dy = ∑ₙ cₙ Γ(s+m) / (4πn)^{s+m}`. -/
theorem lintegral_mellin_horocycleG {s : ℝ} (hs : -(m : ℝ) < s) :
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (Aint y * y ^ (s - 2)) =
      ∑' n : ℕ, ENNReal.ofReal (cf n * Real.Gamma (s + m) / (4 * π * n) ^ (s + m)) := by
  calc ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (Aint y * y ^ (s - 2))
      = ∫⁻ y in Ioi (0 : ℝ), ∑' n : ℕ, ENNReal.ofReal (mtermG s n y) := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
        rw [← (hasSum_mtermG s hy).tsum_eq,
          ENNReal.ofReal_tsum_of_nonneg (fun n => mtermG_nonneg s n hy) (hasSum_mtermG s hy).summable]
    _ = ∑' n : ℕ, ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (mtermG s n y) := by
        refine lintegral_tsum fun n => ?_
        refine (ENNReal.measurable_ofReal.comp ?_).aemeasurable
        unfold mtermG; fun_prop
    _ = _ := by
        refine tsum_congr fun n => ?_
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp [mtermG, cf_zero]
        · rw [← integral_mtermG hs hn, ofReal_integral_eq_lintegral_ofReal (integrableOn_mtermG hs hn)
            ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun y hy =>
              mtermG_nonneg s n hy))]

end RamanujanTau.RankinErrorGeneral

#print axioms RamanujanTau.RankinErrorGeneral.exists_cf_le
#print axioms RamanujanTau.RankinErrorGeneral.lintegral_mellin_horocycleG
