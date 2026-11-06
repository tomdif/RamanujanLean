/-
# The diagonal: `Σ_n n^{−1} V(2 log n − ℓ) = ℓ + 2γ + O((1+|ℓ|) e^{−ℓ/2})`

`V(L) = ∫_{u>L} g`, so the sum is `∫ g(u) H((u+ℓ)/2) du` with `H(v) = Σ_{log n < v} 1/n` the harmonic
number `H_{⌈e^v−1⌉}`. Mathlib's `eulerMascheroniSeq < γ < eulerMascheroniSeq'` gives
`|H(v) − v − γ| ≤ (2+|v|)e^{−v}`, and `∫ g(u)((u+ℓ)/2 + γ) du = ℓ + 2γ` (`∫ g = 2`, `∫ u g = 0`).
-/
import RamanujanTau.ZetaAFE.Split

set_option autoImplicit false

namespace RamanujanTau.ZetaAFE

open MeasureTheory Set Filter Topology

/-- `k(v) = ⌈e^v − 1⌉₊ = #{n ≥ 1 : log n < v}`. -/
noncomputable def kc (v : ℝ) : ℕ := ⌈Real.exp v - 1⌉₊

/-- `H(v) = harmonic (k(v))`. -/
noncomputable def Hv (v : ℝ) : ℝ := (harmonic (kc v) : ℝ)

lemma lt_kc_iff (n : ℕ) (v : ℝ) : n < kc v ↔ lg n < v := by
  unfold kc lg
  rw [Nat.lt_ceil, Real.log_lt_iff_lt_exp (by positivity)]
  constructor <;> intro h <;> linarith

lemma Hv_nonneg (v : ℝ) : 0 ≤ Hv v := by
  unfold Hv harmonic; push_cast; exact Finset.sum_nonneg fun i _ => by positivity

lemma Hv_le (v : ℝ) : Hv v ≤ 1 + |v| := by
  unfold Hv
  by_cases hk : kc v = 0
  · rw [hk]; simp; positivity
  · have h1 := harmonic_le_one_add_log (kc v)
    have hk1 : (1 : ℝ) ≤ kc v := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    have h2 : Real.log (kc v) < v := by
      have := (lt_kc_iff (kc v - 1) v).mp (by omega)
      unfold lg at this
      rwa [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hk), Nat.cast_one, sub_add_cancel] at this
    have : v ≤ |v| := le_abs_self v
    push_cast at h1
    linarith

/-- `|H(v) − v − γ| ≤ (2+|v|) e^{−v}`. -/
theorem abs_Hv_sub_le (v : ℝ) :
    |Hv v - v - Real.eulerMascheroniConstant| ≤ (2 + |v|) * Real.exp (-v) := by
  have hγ1 := Real.one_half_lt_eulerMascheroniConstant
  have hγ2 := Real.eulerMascheroniConstant_lt_two_thirds
  rcases le_or_gt v 0 with hv | hv
  · have hk : kc v = 0 := by
      unfold kc; apply Nat.ceil_eq_zero.mpr
      have := Real.exp_le_one_iff.mpr hv; linarith
    have he : 1 ≤ Real.exp (-v) := Real.one_le_exp (by linarith)
    unfold Hv; rw [hk]; simp
    rw [abs_le]; constructor
    · nlinarith [abs_nonneg v, le_abs_self v, neg_abs_le v]
    · nlinarith [abs_nonneg v, le_abs_self v, neg_abs_le v]
  · set k := kc v with hkdef
    have hk0 : 0 ≤ Real.exp v - 1 := by have := Real.add_one_le_exp v; linarith
    have hkl : (k : ℝ) < Real.exp v := by
      have := Nat.ceil_lt_add_one hk0; rw [hkdef]; unfold kc; linarith
    have hku : Real.exp v - 1 ≤ k := Nat.le_ceil _
    have hk1 : 1 ≤ k := by
      rw [hkdef]; unfold kc
      apply Nat.one_le_iff_ne_zero.mpr; intro h
      rw [Nat.ceil_eq_zero] at h
      have := Real.add_one_lt_exp (ne_of_gt hv); linarith
    have hk1r : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hlogk : Real.log k < v := by rw [Real.log_lt_iff_lt_exp (by linarith)]; exact hkl
    have hlogk1 : v ≤ Real.log (k + 1) := by
      rw [Real.le_log_iff_exp_le (by linarith)]; linarith
    have hs1 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant k
    have hs2 := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' k
    unfold Real.eulerMascheroniSeq at hs1
    unfold Real.eulerMascheroniSeq' at hs2
    rw [if_neg (by omega)] at hs2
    have hlog1 : Real.log (k + 1) - Real.log k ≤ 1 / k := by
      rw [← Real.log_div (by linarith) (by linarith)]
      have := Real.log_le_sub_one_of_pos (x := (k + 1) / k) (by positivity)
      have e : ((k : ℝ) + 1) / k - 1 = 1 / k := by field_simp; ring
      linarith
    have hkinv : 1 / (k : ℝ) ≤ 2 * Real.exp (-v) := by
      rw [Real.exp_neg, div_le_iff₀ (by linarith)]
      have : Real.exp v ≤ 2 * k := by linarith
      calc (1 : ℝ) = Real.exp v * (Real.exp v)⁻¹ := by field_simp
        _ ≤ 2 * k * (Real.exp v)⁻¹ := by gcongr
        _ = _ := by ring
    unfold Hv
    rw [← hkdef]
    rw [abs_le]; constructor
    · have : 0 ≤ |v| * Real.exp (-v) := by positivity
      nlinarith
    · have : 0 ≤ |v| * Real.exp (-v) := by positivity
      nlinarith

/-- The diagonal sum `D(ℓ) = Σ_n V(2 log n − ℓ)/n`. -/
noncomputable def Dsum (ℓ : ℝ) : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) * V (2 * lg n - ℓ)

lemma integrableOn_gk (L : ℝ) : IntegrableOn gk (Ioi L) := integrable_gk.integrableOn

lemma summable_diag (ℓ : ℝ) : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) * V (2 * lg n - ℓ) := by
  have hs := (summable_rpow_neg (σ := 3) (by norm_num)).mul_left (2 * Real.exp ℓ)
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (by positivity) (V_nonneg _)) (fun n => ?_) hs
  have hV := V_le_exp (2 * lg n - ℓ)
  have he : Real.exp (-(2 * lg n - ℓ)) = Real.exp ℓ * ((n : ℝ) + 1) ^ (-(2 : ℝ)) := by
    unfold lg
    rw [Real.rpow_def_of_pos (by positivity), ← Real.exp_add]; congr 1; ring
  have h3 : 1 / ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ (-(2 : ℝ)) = ((n : ℝ) + 1) ^ (-(3 : ℝ)) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
    rw [show (3 : ℝ) = 1 + 2 by norm_num, Real.rpow_add (by positivity), Real.rpow_one]
    field_simp
  calc 1 / ((n : ℝ) + 1) * V (2 * lg n - ℓ) ≤ 1 / ((n : ℝ) + 1) * (2 * Real.exp (-(2 * lg n - ℓ))) := by
        gcongr
    _ = 2 * Real.exp ℓ * (1 / ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ (-(2 : ℝ))) := by rw [he]; ring
    _ = _ := by rw [h3]

/-- `D(ℓ) = ∫ g(u) H((u+ℓ)/2) du`. -/
theorem Dsum_eq_integral (ℓ : ℝ) : Dsum ℓ = ∫ u, gk u * Hv ((u + ℓ) / 2) := by
  unfold Dsum V
  set F : ℕ → ℝ → ℝ := fun n u => 1 / ((n : ℝ) + 1) * (Ioi (2 * lg n - ℓ)).indicator gk u with hF
  have hint : ∀ n, Integrable (F n) := fun n =>
    ((integrable_gk.indicator measurableSet_Ioi).const_mul _)
  have hnorm : ∀ n, ∫ u, ‖F n u‖ = 1 / ((n : ℝ) + 1) * ∫ u in Ioi (2 * lg n - ℓ), gk u := by
    intro n
    have : ∀ u, ‖F n u‖ = F n u := fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact mul_nonneg (by positivity) (indicator_nonneg (fun x _ => (gk_pos x).le) _)
    simp_rw [this, hF]
    rw [integral_const_mul, integral_indicator measurableSet_Ioi]
  have hsum : Summable fun n => ∫ u, ‖F n u‖ := by
    simp_rw [hnorm]; exact summable_diag ℓ
  have hswap := integral_tsum_of_summable_integral_norm hint hsum
  have hl : ∀ n, ∫ u, F n u = 1 / ((n : ℝ) + 1) * ∫ u in Ioi (2 * lg n - ℓ), gk u := by
    intro n; simp only [hF]; rw [integral_const_mul, integral_indicator measurableSet_Ioi]
  simp_rw [hl] at hswap
  rw [hswap]
  congr 1; funext u
  have hpt : ∀ n, F n u = if n < kc ((u + ℓ) / 2) then 1 / ((n : ℝ) + 1) * gk u else 0 := by
    intro n
    simp only [hF]
    by_cases h : n < kc ((u + ℓ) / 2)
    · rw [if_pos h, indicator_of_mem]
      rw [mem_Ioi]; have := (lt_kc_iff n _).mp h; linarith
    · rw [if_neg h, indicator_of_notMem, mul_zero]
      rw [mem_Ioi, not_lt]; have := (lt_kc_iff n _).not.mp h; push_neg at this; linarith
  simp_rw [hpt]
  rw [tsum_eq_sum (s := Finset.range (kc ((u + ℓ) / 2))) (fun n hn => by
    rw [if_neg]; simpa using hn)]
  rw [Finset.sum_ite_of_true (fun n hn => Finset.mem_range.mp hn), ← Finset.sum_mul]
  unfold Hv harmonic
  push_cast
  rw [mul_comm]
  congr 1
  refine Finset.sum_congr rfl fun n _ => by rw [one_div]

lemma integral_mul_gk_zero : ∫ u, u * gk u = 0 := by
  have h := integral_neg_eq_self (fun u => u * gk u) volume
  have hodd : (fun u : ℝ => -u * gk (-u)) = fun u => -(u * gk u) := by
    funext u; simp [gk]
  simp only [hodd, integral_neg] at h
  linarith

lemma integrable_mul_gk : Integrable fun u : ℝ => u * gk u := by
  have h := (integrable_mul_exp_neg_mul_sq (b := 1 / 4) (by norm_num)).const_mul (1 / Real.sqrt Real.pi)
  refine h.congr (Eventually.of_forall fun u => ?_)
  simp only [gk_eq]; ring

lemma bound_fun_integrable :
    Integrable fun u : ℝ => gk u * (2 + |u|) * Real.exp (-u / 2) := by
  have h := (integrable_exp_neg_mul_sq (b := 1 / 8) (by norm_num)).const_mul
    (2 * Real.exp (9 / 2) / Real.sqrt Real.pi)
  refine h.mono' (Continuous.aestronglyMeasurable (by unfold gk; fun_prop))
    (Eventually.of_forall fun u => ?_)
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  rw [Real.norm_eq_abs, abs_of_nonneg (by have := gk_pos u; positivity)]
  unfold gk
  have h1 : 2 + |u| ≤ 2 * Real.exp |u| := by
    have := Real.add_one_le_exp |u|; have := abs_nonneg u; linarith
  have h2 : Real.exp (-u / 2) ≤ Real.exp (|u| / 2) := by
    apply Real.exp_le_exp.mpr; have := neg_abs_le u; linarith
  have h3 : Real.exp (-(u ^ 2) / 4) * Real.exp |u| * Real.exp (|u| / 2) ≤
      Real.exp (9 / 2) * Real.exp (-(1 / 8) * u ^ 2) := by
    simp only [← Real.exp_add]; apply Real.exp_le_exp.mpr
    have : |u| ^ 2 = u ^ 2 := sq_abs u
    nlinarith [sq_nonneg (|u| - 6)]
  calc Real.exp (-u ^ 2 / 4) / Real.sqrt Real.pi * (2 + |u|) * Real.exp (-u / 2)
      ≤ Real.exp (-u ^ 2 / 4) / Real.sqrt Real.pi * (2 * Real.exp |u|) * Real.exp (|u| / 2) := by
        gcongr
    _ = 2 / Real.sqrt Real.pi * (Real.exp (-(u ^ 2) / 4) * Real.exp |u| * Real.exp (|u| / 2)) := by
        ring_nf
    _ ≤ 2 / Real.sqrt Real.pi * (Real.exp (9 / 2) * Real.exp (-(1 / 8) * u ^ 2)) := by gcongr
    _ = _ := by ring

/-- `A_D = ∫ g(u)(2+|u|)e^{−u/2} du`. -/
noncomputable def AD : ℝ := ∫ u, gk u * (2 + |u|) * Real.exp (-u / 2)

/-- **Diagonal asymptotics.** `|D(ℓ) − ℓ − 2γ| ≤ A_D (1+|ℓ|) e^{−ℓ/2}`. -/
theorem abs_Dsum_sub_le (ℓ : ℝ) :
    |Dsum ℓ - ℓ - 2 * Real.eulerMascheroniConstant| ≤ AD * (1 + |ℓ|) * Real.exp (-ℓ / 2) := by
  rw [Dsum_eq_integral]
  set γ := Real.eulerMascheroniConstant
  have hmain : ∫ u, gk u * ((u + ℓ) / 2 + γ) = ℓ + 2 * γ := by
    have : (fun u => gk u * ((u + ℓ) / 2 + γ)) = fun u => (1 / 2) * (u * gk u) + (ℓ / 2 + γ) * gk u := by
      funext u; ring
    rw [this, integral_add (integrable_mul_gk.const_mul _) (integrable_gk.const_mul _),
      integral_const_mul, integral_const_mul, integral_mul_gk_zero, integral_gk]
    ring
  have hmeas : Measurable fun u : ℝ => Hv ((u + ℓ) / 2) := by
    unfold Hv kc
    refine (measurable_from_nat (f := fun k : ℕ => ((harmonic k : ℚ) : ℝ))).comp ?_
    exact Nat.measurable_ceil.comp (by fun_prop)
  have hgH : Integrable fun u => gk u * Hv ((u + ℓ) / 2) := by
    have hb : Integrable fun u : ℝ => (1 + |ℓ|) * gk u + |u| * gk u := by
      refine (integrable_gk.const_mul _).add ?_
      refine integrable_mul_gk.norm.congr (Eventually.of_forall fun u => ?_)
      simp [Real.norm_eq_abs, abs_mul, abs_of_pos (gk_pos u)]
    refine hb.mono' (continuous_gk.measurable.mul hmeas).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (gk_pos u), abs_of_nonneg (Hv_nonneg _)]
    have h1 := Hv_le ((u + ℓ) / 2)
    have h2 : |(u + ℓ) / 2| ≤ |ℓ| + |u| := by
      rw [abs_div, abs_two]
      have := abs_add_le u ℓ
      have := abs_nonneg u; have := abs_nonneg ℓ
      linarith
    have := gk_pos u
    nlinarith
  have haff : Integrable fun u => gk u * ((u + ℓ) / 2 + γ) := by
    have : (fun u => gk u * ((u + ℓ) / 2 + γ)) = fun u => (1 / 2) * (u * gk u) + (ℓ / 2 + γ) * gk u := by
      funext u; ring
    rw [this]; exact (integrable_mul_gk.const_mul _).add (integrable_gk.const_mul _)
  have hdiff : (∫ u, gk u * Hv ((u + ℓ) / 2)) - ℓ - 2 * γ =
      ∫ u, gk u * (Hv ((u + ℓ) / 2) - (u + ℓ) / 2 - γ) := by
    rw [sub_sub, ← hmain, ← integral_sub hgH haff]
    congr 1; funext u; ring
  rw [hdiff, ← Real.norm_eq_abs]
  have hbd : Integrable fun u : ℝ => (1 + |ℓ|) * Real.exp (-ℓ / 2) *
      (gk u * (2 + |u|) * Real.exp (-u / 2)) := bound_fun_integrable.const_mul _
  refine (norm_integral_le_of_norm_le hbd (Eventually.of_forall fun u => ?_)).trans (le_of_eq ?_)
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (gk_pos u)]
    have h := abs_Hv_sub_le ((u + ℓ) / 2)
    have hv : |(u + ℓ) / 2| ≤ (|u| + |ℓ|) / 2 := by
      rw [abs_div, abs_two]; have := abs_add_le u ℓ; linarith
    have he : Real.exp (-((u + ℓ) / 2)) = Real.exp (-ℓ / 2) * Real.exp (-u / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [he] at h
    have hgk := gk_pos u
    have hE1 := Real.exp_pos (-ℓ / 2)
    have hE2 := Real.exp_pos (-u / 2)
    have hfac : 2 + |(u + ℓ) / 2| ≤ (1 + |ℓ|) * (2 + |u|) := by
      have := abs_nonneg u; have := abs_nonneg ℓ; nlinarith
    calc gk u * |Hv ((u + ℓ) / 2) - (u + ℓ) / 2 - γ|
        ≤ gk u * ((2 + |(u + ℓ) / 2|) * (Real.exp (-ℓ / 2) * Real.exp (-u / 2))) := by gcongr
      _ ≤ gk u * (((1 + |ℓ|) * (2 + |u|)) * (Real.exp (-ℓ / 2) * Real.exp (-u / 2))) := by gcongr
      _ = _ := by ring
  · rw [integral_const_mul]; unfold AD; ring

end RamanujanTau.ZetaAFE
