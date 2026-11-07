/-
# The Δ diagonal with the `V` weight

`H(v) = A(⌈e^v − 1⌉) = Σ_{log n < v} a(n)²/n` satisfies `|H(v) − c₀v − γ_Δ| ≤ C(2+|v|)e^{−v/5}`;
hence `D(L) = Σ_n a(n)²/n · V(2 log n − L) = ∫ g(u) H((u+L)/2) du = c₀L + 2γ_Δ + O((1+|L|)e^{−L/10})`.
-/
import RamanujanTau.GoodSecondTerm.DiagD
import RamanujanTau.ZetaAFE.Diag

set_option autoImplicit false

namespace RamanujanTau.GoodSecondTerm

open MeasureTheory Set Filter Topology
open RamanujanTau.ZetaAFE

noncomputable def HtD (v : ℝ) : ℝ := AA (kc v)

lemma AA_eq_range (k : ℕ) : AA k = ∑ m ∈ Finset.range k, bb (m + 1) / ((m : ℝ) + 1) := by
  induction k with
  | zero => simp [AA]
  | succ k ih => rw [AA_succ, ih, Finset.sum_range_succ]; push_cast; ring

lemma AA_nonneg (k : ℕ) : 0 ≤ AA k := by
  unfold AA; exact Finset.sum_nonneg fun n _ => div_nonneg (bb_nonneg n) (Nat.cast_nonneg _)

theorem abs_HtD_sub_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ,
    |HtD v - c0 * v - gammaD| ≤ C * (2 + |v|) * Real.exp (-v / 5) := by
  obtain ⟨C, hC0, hC⟩ := AA_asymp
  refine ⟨C + 2 * |c0| + |gammaD|, by positivity, fun v => ?_⟩
  have hX : 0 ≤ C + 2 * |c0| + |gammaD| := by positivity
  rcases le_or_gt v 0 with hv | hv
  · have hk : kc v = 0 := by
      unfold kc; apply Nat.ceil_eq_zero.mpr
      have := Real.exp_le_one_iff.mpr hv; linarith
    have he : 1 ≤ Real.exp (-v / 5) := Real.one_le_exp (by linarith)
    unfold HtD; rw [hk, show AA 0 = 0 by unfold AA; simp]
    rw [show (0 : ℝ) - c0 * v - gammaD = -(c0 * v + gammaD) by ring, abs_neg]
    have h1 : |c0 * v + gammaD| ≤ |c0| * |v| + |gammaD| := by
      refine (abs_add_le _ _).trans ?_; rw [abs_mul]
    have h2 : |c0| * |v| + |gammaD| ≤ (C + 2 * |c0| + |gammaD|) * (2 + |v|) := by
      have := abs_nonneg c0; have := abs_nonneg v; have := abs_nonneg gammaD; nlinarith
    have h3 : 0 ≤ (C + 2 * |c0| + |gammaD|) * (2 + |v|) := by positivity
    nlinarith
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
    have hlog1 : Real.log (k + 1) - Real.log k ≤ 1 / k := by
      rw [← Real.log_div (by linarith) (by linarith)]
      have := Real.log_le_sub_one_of_pos (x := (k + 1) / k) (by positivity)
      have e : ((k : ℝ) + 1) / k - 1 = 1 / k := by field_simp; ring
      linarith
    have hinv : 1 / (k : ℝ) ≤ (k : ℝ) ^ (-(1 / 5 : ℝ)) := by
      rw [one_div, ← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hk1r (by norm_num)
    have hkp : (k : ℝ) ^ (-(1 / 5 : ℝ)) ≤ 2 * Real.exp (-v / 5) := by
      have h2k : Real.exp v / 2 ≤ k := by linarith
      calc (k : ℝ) ^ (-(1 / 5 : ℝ)) ≤ (Real.exp v / 2) ^ (-(1 / 5 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) h2k (by norm_num)
        _ = 2 ^ (1 / 5 : ℝ) * Real.exp (-v / 5) := by
            rw [Real.div_rpow (Real.exp_pos v).le (by norm_num), ← Real.exp_mul,
              Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), div_inv_eq_mul,
              show v * -(1 / 5 : ℝ) = -v / 5 by ring]
            ring
        _ ≤ 2 * Real.exp (-v / 5) := by
            gcongr
            calc (2 : ℝ) ^ (1 / 5 : ℝ) ≤ 2 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 2 := Real.rpow_one 2
    have hA := hC k hk1
    unfold HtD; rw [← hkdef]
    have hcv : |c0 * Real.log k - c0 * v| ≤ |c0| * (k : ℝ) ^ (-(1 / 5 : ℝ)) := by
      rw [← mul_sub, abs_mul]
      gcongr
      rw [abs_le]; constructor <;> linarith
    have hE := Real.exp_pos (-v / 5)
    calc |AA k - c0 * v - gammaD| = |(AA k - c0 * Real.log k - gammaD) + (c0 * Real.log k - c0 * v)| := by
          ring_nf
      _ ≤ C * (k : ℝ) ^ (-(1 / 5 : ℝ)) + |c0| * (k : ℝ) ^ (-(1 / 5 : ℝ)) :=
          (abs_add_le _ _).trans (add_le_add hA hcv)
      _ = (C + |c0|) * (k : ℝ) ^ (-(1 / 5 : ℝ)) := by ring
      _ ≤ (C + |c0|) * (2 * Real.exp (-v / 5)) := by gcongr
      _ ≤ (C + 2 * |c0| + |gammaD|) * (2 + |v|) * Real.exp (-v / 5) := by
          have := abs_nonneg c0; have := abs_nonneg gammaD; have := abs_nonneg v
          have hk2 : 2 * (C + |c0|) ≤ (C + 2 * |c0| + |gammaD|) * (2 + |v|) := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_right hk2 hE.le]

lemma HtD_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, HtD v ≤ C * (1 + |v|) := by
  obtain ⟨C, hC0, hC⟩ := abs_HtD_sub_le
  refine ⟨|c0| + |gammaD| + 2 * C, by positivity, fun v => ?_⟩
  rcases le_or_gt v 0 with hv | hv
  · have hk : kc v = 0 := by
      unfold kc; apply Nat.ceil_eq_zero.mpr
      have := Real.exp_le_one_iff.mpr hv; linarith
    unfold HtD; rw [hk, show AA 0 = 0 by unfold AA; simp]; positivity
  · have h := hC v
    have he : Real.exp (-v / 5) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h1 : HtD v ≤ c0 * v + gammaD + C * (2 + |v|) * Real.exp (-v / 5) := by
      have := (abs_le.mp h).2; linarith
    have h2 : C * (2 + |v|) * Real.exp (-v / 5) ≤ C * (2 + |v|) := by
      have : 0 ≤ C * (2 + |v|) := by positivity
      nlinarith [Real.exp_pos (-v / 5)]
    have h3 : c0 * v ≤ |c0| * |v| := by
      rw [← abs_mul]; exact le_abs_self _
    have := abs_nonneg c0; have := abs_nonneg v; have := le_abs_self gammaD
    nlinarith [mul_nonneg hC0 (abs_nonneg v), mul_nonneg (abs_nonneg gammaD) (abs_nonneg v)]

/-- `D(L) = Σ_n a(n)²/n · V(2 log n − L)`. -/
noncomputable def DsumD (L : ℝ) : ℝ := ∑' n : ℕ, bb (n + 1) / ((n : ℝ) + 1) * V (2 * lg n - L)

lemma bb_shift_eq (n : ℕ) (L : ℝ) :
    bb (n + 1) / ((n : ℝ) + 1) * Real.exp (-(2 * lg n - L)) =
      Real.exp L * (|((tau (n + 1) : ℤ) : ℝ)| * ((n : ℝ) + 1) ^ (-(7 : ℝ))) ^ 2 := by
  have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 : Real.exp (-(2 * lg n - L)) = Real.exp L * (((n : ℝ) + 1) ^ 2)⁻¹ := by
    rw [show -(2 * lg n - L) = L + -(2 * lg n) by ring, Real.exp_add]
    unfold lg; rw [show -(2 * Real.log ((n : ℝ) + 1)) = -(Real.log (((n : ℝ) + 1) ^ 2)) by
      rw [Real.log_pow]; push_cast; ring, Real.exp_neg, Real.exp_log (by positivity)]
  have h7 : ((n : ℝ) + 1) ^ (-(7 : ℝ)) = (((n : ℝ) + 1) ^ (7 : ℕ))⁻¹ := by
    rw [Real.rpow_neg hp.le]; norm_cast
  rw [h1, h7, mul_pow, sq_abs]
  unfold bb
  push_cast
  field_simp

lemma summable_diagD (L : ℝ) : Summable fun n : ℕ => bb (n + 1) / ((n : ℝ) + 1) * V (2 * lg n - L) := by
  set x : ℕ → ℝ := fun n => |((tau (n + 1) : ℤ) : ℝ)| * ((n : ℝ) + 1) ^ (-(7 : ℝ)) with hx
  have hs : Summable x := summable_abs_tau_shift (σ := 7) (by norm_num)
  have hx0 : ∀ n, 0 ≤ x n := fun n => by simp only [hx]; positivity
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (div_nonneg (bb_nonneg _) (by positivity))
    (V_nonneg _)) (fun n => ?_) ((hs.mul_left (2 * Real.exp L * (∑' m, x m))))
  have hV := V_le_exp (2 * lg n - L)
  have hle : x n ≤ ∑' m, x m := hs.le_tsum n (fun m _ => hx0 m)
  have h0 : 0 ≤ bb (n + 1) / ((n : ℝ) + 1) := div_nonneg (bb_nonneg _) (by positivity)
  calc bb (n + 1) / ((n : ℝ) + 1) * V (2 * lg n - L)
      ≤ bb (n + 1) / ((n : ℝ) + 1) * (2 * Real.exp (-(2 * lg n - L))) := by gcongr
    _ = 2 * Real.exp L * (x n * x n) := by
        rw [mul_left_comm, bb_shift_eq]; simp only [hx]; ring
    _ ≤ 2 * Real.exp L * (∑' m, x m) * x n := by
        have := hx0 n
        have : x n * x n ≤ (∑' m, x m) * x n := mul_le_mul_of_nonneg_right hle this
        nlinarith [Real.exp_pos L]

/-- `D(L) = ∫ g(u) H((u+L)/2) du`. -/
theorem DsumD_eq_integral (L : ℝ) : DsumD L = ∫ u, gk u * HtD ((u + L) / 2) := by
  unfold DsumD V
  set F : ℕ → ℝ → ℝ := fun n u => bb (n + 1) / ((n : ℝ) + 1) * (Ioi (2 * lg n - L)).indicator gk u
    with hF
  have hw : ∀ n, 0 ≤ bb (n + 1) / ((n : ℝ) + 1) := fun n => div_nonneg (bb_nonneg _) (by positivity)
  have hint : ∀ n, Integrable (F n) := fun n =>
    ((integrable_gk.indicator measurableSet_Ioi).const_mul _)
  have hnorm : ∀ n, ∫ u, ‖F n u‖ = bb (n + 1) / ((n : ℝ) + 1) * ∫ u in Ioi (2 * lg n - L), gk u := by
    intro n
    have : ∀ u, ‖F n u‖ = F n u := fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact mul_nonneg (hw n) (indicator_nonneg (fun x _ => (gk_pos x).le) _)
    simp_rw [this, hF]
    rw [integral_const_mul, integral_indicator measurableSet_Ioi]
  have hsum : Summable fun n => ∫ u, ‖F n u‖ := by
    simp_rw [hnorm]; exact summable_diagD L
  have hswap := integral_tsum_of_summable_integral_norm hint hsum
  have hl : ∀ n, ∫ u, F n u = bb (n + 1) / ((n : ℝ) + 1) * ∫ u in Ioi (2 * lg n - L), gk u := by
    intro n; simp only [hF]; rw [integral_const_mul, integral_indicator measurableSet_Ioi]
  simp_rw [hl] at hswap
  rw [hswap]
  congr 1; funext u
  have hpt : ∀ n, F n u = if n < kc ((u + L) / 2) then bb (n + 1) / ((n : ℝ) + 1) * gk u else 0 := by
    intro n
    simp only [hF]
    by_cases h : n < kc ((u + L) / 2)
    · rw [if_pos h, indicator_of_mem]
      rw [mem_Ioi]; have := (lt_kc_iff n _).mp h; linarith
    · rw [if_neg h, indicator_of_notMem, mul_zero]
      rw [mem_Ioi, not_lt]; have := (lt_kc_iff n _).not.mp h; push_neg at this; linarith
  simp_rw [hpt]
  rw [tsum_eq_sum (s := Finset.range (kc ((u + L) / 2))) (fun n hn => by
    rw [if_neg]; simpa using hn)]
  rw [Finset.sum_ite_of_true (fun n hn => Finset.mem_range.mp hn), ← Finset.sum_mul]
  unfold HtD
  rw [AA_eq_range, mul_comm]

lemma bound_fun_integrable_D :
    Integrable fun u : ℝ => gk u * (2 + |u|) * Real.exp (-u / 10) := by
  have h := (integrable_exp_neg_mul_sq (b := 1 / 8) (by norm_num)).const_mul
    (2 * Real.exp (9 / 2) / Real.sqrt Real.pi)
  refine h.mono' (Continuous.aestronglyMeasurable (by unfold gk; fun_prop))
    (Eventually.of_forall fun u => ?_)
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  rw [Real.norm_eq_abs, abs_of_nonneg (by have := gk_pos u; positivity)]
  unfold gk
  have h1 : 2 + |u| ≤ 2 * Real.exp |u| := by
    have := Real.add_one_le_exp |u|; have := abs_nonneg u; linarith
  have h2 : Real.exp (-u / 10) ≤ Real.exp (|u| / 2) := by
    apply Real.exp_le_exp.mpr; have := neg_abs_le u; have := abs_nonneg u; linarith
  have h3 : Real.exp (-(u ^ 2) / 4) * Real.exp |u| * Real.exp (|u| / 2) ≤
      Real.exp (9 / 2) * Real.exp (-(1 / 8) * u ^ 2) := by
    simp only [← Real.exp_add]; apply Real.exp_le_exp.mpr
    have : |u| ^ 2 = u ^ 2 := sq_abs u
    nlinarith [sq_nonneg (|u| - 6)]
  calc Real.exp (-u ^ 2 / 4) / Real.sqrt Real.pi * (2 + |u|) * Real.exp (-u / 10)
      ≤ Real.exp (-u ^ 2 / 4) / Real.sqrt Real.pi * (2 * Real.exp |u|) * Real.exp (|u| / 2) := by
        gcongr
    _ = 2 / Real.sqrt Real.pi * (Real.exp (-(u ^ 2) / 4) * Real.exp |u| * Real.exp (|u| / 2)) := by
        ring_nf
    _ ≤ 2 / Real.sqrt Real.pi * (Real.exp (9 / 2) * Real.exp (-(1 / 8) * u ^ 2)) := by gcongr
    _ = _ := by ring

noncomputable def ADD : ℝ := ∫ u, gk u * (2 + |u|) * Real.exp (-u / 10)

/-- **Δ diagonal asymptotics**: `|D(L) − c₀L − 2γ_Δ| ≤ C (1+|L|) e^{−L/10}`. -/
theorem abs_DsumD_sub_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ,
    |DsumD L - c0 * L - 2 * gammaD| ≤ C * (1 + |L|) * Real.exp (-L / 10) := by
  obtain ⟨C4, hC40, hC4⟩ := abs_HtD_sub_le
  obtain ⟨C6, hC60, hC6⟩ := HtD_le
  have hADD : 0 ≤ ADD := integral_nonneg fun u => by have := gk_pos u; positivity
  refine ⟨C4 * ADD, by positivity, fun L => ?_⟩
  rw [DsumD_eq_integral]
  set γ := gammaD
  have hmain : ∫ u, gk u * (c0 * ((u + L) / 2) + γ) = c0 * L + 2 * γ := by
    have : (fun u => gk u * (c0 * ((u + L) / 2) + γ)) =
        fun u => (c0 / 2) * (u * gk u) + (c0 * L / 2 + γ) * gk u := by funext u; ring
    rw [this, integral_add (integrable_mul_gk.const_mul _) (integrable_gk.const_mul _),
      integral_const_mul, integral_const_mul, integral_mul_gk_zero, integral_gk]
    ring
  have hmeas : Measurable fun u : ℝ => HtD ((u + L) / 2) := by
    unfold HtD kc
    refine (measurable_from_nat (f := AA)).comp ?_
    exact Nat.measurable_ceil.comp (by fun_prop)
  have hgH : Integrable fun u => gk u * HtD ((u + L) / 2) := by
    have hb : Integrable fun u : ℝ => C6 * (1 + |L|) * gk u + C6 * (|u| * gk u) := by
      refine (integrable_gk.const_mul _).add (Integrable.const_mul ?_ _)
      refine integrable_mul_gk.norm.congr (Eventually.of_forall fun u => ?_)
      simp [Real.norm_eq_abs, abs_mul, abs_of_pos (gk_pos u)]
    refine hb.mono' (continuous_gk.measurable.mul hmeas).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    have h0 : 0 ≤ HtD ((u + L) / 2) := by unfold HtD; exact AA_nonneg _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (gk_pos u), abs_of_nonneg h0]
    have h1 := hC6 ((u + L) / 2)
    have h2 : |(u + L) / 2| ≤ |L| + |u| := by
      rw [abs_div, abs_two]
      have := abs_add_le u L
      have := abs_nonneg u; have := abs_nonneg L
      linarith
    have := gk_pos u
    have h3 : HtD ((u + L) / 2) ≤ C6 * (1 + |L|) + C6 * |u| := by nlinarith
    nlinarith
  have haff : Integrable fun u => gk u * (c0 * ((u + L) / 2) + γ) := by
    have : (fun u => gk u * (c0 * ((u + L) / 2) + γ)) =
        fun u => (c0 / 2) * (u * gk u) + (c0 * L / 2 + γ) * gk u := by funext u; ring
    rw [this]; exact (integrable_mul_gk.const_mul _).add (integrable_gk.const_mul _)
  have hdiff : (∫ u, gk u * HtD ((u + L) / 2)) - c0 * L - 2 * γ =
      ∫ u, gk u * (HtD ((u + L) / 2) - c0 * ((u + L) / 2) - γ) := by
    rw [sub_sub, ← hmain, ← integral_sub hgH haff]
    congr 1; funext u; ring
  rw [hdiff, ← Real.norm_eq_abs]
  have hbd : Integrable fun u : ℝ => C4 * (1 + |L|) * Real.exp (-L / 10) *
      (gk u * (2 + |u|) * Real.exp (-u / 10)) := bound_fun_integrable_D.const_mul _
  refine (norm_integral_le_of_norm_le hbd (Eventually.of_forall fun u => ?_)).trans (le_of_eq ?_)
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (gk_pos u)]
    have h := hC4 ((u + L) / 2)
    have he : Real.exp (-((u + L) / 2) / 5) = Real.exp (-L / 10) * Real.exp (-u / 10) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [he] at h
    have hgk := gk_pos u
    have hE1 := Real.exp_pos (-L / 10)
    have hE2 := Real.exp_pos (-u / 10)
    have hfac : 2 + |(u + L) / 2| ≤ (1 + |L|) * (2 + |u|) := by
      have hv : |(u + L) / 2| ≤ (|u| + |L|) / 2 := by
        rw [abs_div, abs_two]; have := abs_add_le u L; linarith
      have := abs_nonneg u; have := abs_nonneg L; nlinarith
    calc gk u * |HtD ((u + L) / 2) - c0 * ((u + L) / 2) - γ|
        ≤ gk u * (C4 * (2 + |(u + L) / 2|) * (Real.exp (-L / 10) * Real.exp (-u / 10))) := by gcongr
      _ ≤ gk u * (C4 * ((1 + |L|) * (2 + |u|)) * (Real.exp (-L / 10) * Real.exp (-u / 10))) := by
          gcongr
      _ = _ := by ring
  · rw [integral_const_mul]; unfold ADD; ring

end RamanujanTau.GoodSecondTerm
