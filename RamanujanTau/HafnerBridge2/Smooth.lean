/-
# Item (c), part 1: the `V`-smoothed sum of a sequence with a log asymptotic

For any real sequence `f` (indexed by `m`, standing for `n = m + 1`) with partial sums
`S(k) = Σ_{m<k} f(m)` satisfying `|S(k) − c log k − K| ≤ E k^{−1/5}` (`k ≥ 1`):

    |Σ_m f(m) V(2 log(m+1) − L) − cL − 2K| ≤ ADD · (E + 2|c| + |K|) · (1+|L|) e^{−L/10}.

This is `GoodSecondTerm.abs_DsumD_sub_le` with the sequence abstracted and nonnegativity removed;
the boundary constant `2K` comes from `∫ g = 2` and `∫ u g = 0` (symmetry of `V`).
-/
import RamanujanTau.HafnerBridge2.Twisted

set_option autoImplicit false

namespace RamanujanTau.HafnerBridge2

open MeasureTheory Set Filter Topology
open RamanujanTau.ZetaAFE RamanujanTau.GoodSecondTerm

section
variable {f : ℕ → ℝ} {c K E : ℝ}

/-- `S(k) = Σ_{m<k} f(m)`. -/
noncomputable def Sp (f : ℕ → ℝ) (k : ℕ) : ℝ := ∑ m ∈ Finset.range k, f m

/-- `H(v) = S(k(v))`. -/
noncomputable def Ht (f : ℕ → ℝ) (v : ℝ) : ℝ := Sp f (kc v)

def LogAsym (f : ℕ → ℝ) (c K E : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → |Sp f k - c * Real.log k - K| ≤ E * (k : ℝ) ^ (-(1 / 5 : ℝ))

variable (hE : 0 ≤ E) (hS : LogAsym f c K E)
include hE hS

theorem abs_Ht_sub_le (v : ℝ) :
    |Ht f v - c * v - K| ≤ (E + 2 * |c| + |K|) * (2 + |v|) * Real.exp (-v / 5) := by
  have hX : 0 ≤ E + 2 * |c| + |K| := by positivity
  rcases le_or_gt v 0 with hv | hv
  · have hk : kc v = 0 := by
      unfold kc; apply Nat.ceil_eq_zero.mpr
      have := Real.exp_le_one_iff.mpr hv; linarith
    have he : 1 ≤ Real.exp (-v / 5) := Real.one_le_exp (by linarith)
    unfold Ht; rw [hk, show Sp f 0 = 0 by simp [Sp]]
    rw [show (0 : ℝ) - c * v - K = -(c * v + K) by ring, abs_neg]
    have h1 : |c * v + K| ≤ |c| * |v| + |K| := by
      refine (abs_add_le _ _).trans ?_; rw [abs_mul]
    have h2 : |c| * |v| + |K| ≤ (E + 2 * |c| + |K|) * (2 + |v|) := by
      have := abs_nonneg c; have := abs_nonneg v; have := abs_nonneg K; nlinarith
    have h3 : 0 ≤ (E + 2 * |c| + |K|) * (2 + |v|) := by positivity
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
    have hA := hS k hk1
    unfold Ht; rw [← hkdef]
    have hcv : |c * Real.log k - c * v| ≤ |c| * (k : ℝ) ^ (-(1 / 5 : ℝ)) := by
      rw [← mul_sub, abs_mul]
      gcongr
      rw [abs_le]; constructor <;> linarith
    have hE' := Real.exp_pos (-v / 5)
    calc |Sp f k - c * v - K| = |(Sp f k - c * Real.log k - K) + (c * Real.log k - c * v)| := by
          ring_nf
      _ ≤ E * (k : ℝ) ^ (-(1 / 5 : ℝ)) + |c| * (k : ℝ) ^ (-(1 / 5 : ℝ)) :=
          (abs_add_le _ _).trans (add_le_add hA hcv)
      _ = (E + |c|) * (k : ℝ) ^ (-(1 / 5 : ℝ)) := by ring
      _ ≤ (E + |c|) * (2 * Real.exp (-v / 5)) := by gcongr
      _ ≤ (E + 2 * |c| + |K|) * (2 + |v|) * Real.exp (-v / 5) := by
          have := abs_nonneg c; have := abs_nonneg K; have := abs_nonneg v
          have hk2 : 2 * (E + |c|) ≤ (E + 2 * |c| + |K|) * (2 + |v|) := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_right hk2 hE'.le]

lemma abs_Ht_le (v : ℝ) : |Ht f v| ≤ 3 * (E + 2 * |c| + |K|) * (1 + |v|) := by
  set Z := E + 2 * |c| + |K| with hZ
  have hZ0 : 0 ≤ Z := by positivity
  rcases le_or_gt v 0 with hv | hv
  · have hk : kc v = 0 := by
      unfold kc; apply Nat.ceil_eq_zero.mpr
      have := Real.exp_le_one_iff.mpr hv; linarith
    unfold Ht; rw [hk, show Sp f 0 = 0 by simp [Sp], abs_zero]; positivity
  · have h := abs_Ht_sub_le hE hS v
    have he : Real.exp (-v / 5) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h2 : Z * (2 + |v|) * Real.exp (-v / 5) ≤ Z * (2 + |v|) := by
      have : 0 ≤ Z * (2 + |v|) := by positivity
      nlinarith [Real.exp_pos (-v / 5)]
    have h3 : |c * v + K| ≤ |c| * |v| + |K| := by
      refine (abs_add_le _ _).trans ?_; rw [abs_mul]
    have e : Ht f v = (Ht f v - c * v - K) + (c * v + K) := by ring
    rw [e]
    have := abs_nonneg c; have := abs_nonneg v; have := abs_nonneg K
    calc |(Ht f v - c * v - K) + (c * v + K)| ≤ |Ht f v - c * v - K| + |c * v + K| := abs_add_le _ _
      _ ≤ Z * (2 + |v|) + (|c| * |v| + |K|) := by linarith
      _ ≤ 3 * Z * (1 + |v|) := by rw [hZ]; nlinarith [mul_nonneg hE (abs_nonneg v)]

lemma abs_Sp_le (k : ℕ) : |Sp f k| ≤ (E + 2 * |c| + |K|) * (1 + k) := by
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; simp [Sp]; positivity
  · have hk : (1 : ℝ) ≤ k := by exact_mod_cast h
    have h1 := hS k h
    have hlog : Real.log k ≤ k := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    have hlog0 : 0 ≤ Real.log k := Real.log_nonneg hk
    have hp : (k : ℝ) ^ (-(1 / 5 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hk (by norm_num)
    have e : Sp f k = (Sp f k - c * Real.log k - K) + (c * Real.log k + K) := by ring
    rw [e]
    have := abs_nonneg c; have := abs_nonneg K
    calc _ ≤ |Sp f k - c * Real.log k - K| + (|c| * Real.log k + |K|) := by
          refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
          refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_of_nonneg hlog0]
      _ ≤ E * 1 + (|c| * k + |K|) := by
          gcongr
          · exact h1.trans (mul_le_mul_of_nonneg_left hp hE)
      _ ≤ _ := by nlinarith

lemma abs_f_le (m : ℕ) : |f m| ≤ 3 * (E + 2 * |c| + |K|) * ((m : ℝ) + 1) := by
  have e : f m = Sp f (m + 1) - Sp f m := by simp [Sp, Finset.sum_range_succ]
  rw [e]
  have h1 := abs_Sp_le hE hS (m + 1)
  have h2 := abs_Sp_le hE hS m
  have hZ : 0 ≤ E + 2 * |c| + |K| := by positivity
  push_cast at h1
  calc _ ≤ |Sp f (m + 1)| + |Sp f m| := abs_sub _ _
    _ ≤ _ := by nlinarith

lemma summable_absf_V (L : ℝ) : Summable fun m : ℕ => |f m| * V (2 * lg m - L) := by
  set Z := E + 2 * |c| + |K| with hZ
  have hZ0 : 0 ≤ Z := by positivity
  set c2 : ℝ := Real.exp (2 ^ 2) / (2 * Real.sqrt Real.pi)
  have hc2 : 0 ≤ c2 := by positivity
  have hsum : Summable fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2 := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simpa using this
  refine Summable.of_nonneg_of_le (fun m => mul_nonneg (abs_nonneg _) (V_nonneg _)) (fun m => ?_)
    (hsum.mul_left (3 * Z * c2 * Real.exp (2 * L)))
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hV := RamanujanTau.GoodSecondTerm2.V_le_exp_k (k := 2) (by norm_num) (2 * lg m - L)
  have he : Real.exp (-(2 * (2 * lg m - L))) = Real.exp (2 * L) / ((m : ℝ) + 1) ^ 4 := by
    rw [show -(2 * (2 * lg m - L)) = 2 * L - 4 * lg m by ring, Real.exp_sub]
    unfold lg
    rw [show (4 : ℝ) * Real.log ((m : ℝ) + 1) = Real.log (((m : ℝ) + 1) ^ 4) by
      rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]
  rw [he] at hV
  have hf := abs_f_le hE hS m
  calc |f m| * V (2 * lg m - L) ≤ (3 * Z * ((m : ℝ) + 1)) * (c2 * (Real.exp (2 * L) / ((m : ℝ) + 1) ^ 4)) :=
        mul_le_mul hf hV (V_nonneg _) (by positivity)
    _ = 3 * Z * c2 * Real.exp (2 * L) * (((m : ℝ) + 1) / ((m : ℝ) + 1) ^ 4) := by ring
    _ ≤ 3 * Z * c2 * Real.exp (2 * L) * (1 / ((m : ℝ) + 1) ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
        nlinarith [pow_pos hm 2, pow_pos hm 3]

lemma summable_f_V (L : ℝ) : Summable fun m : ℕ => f m * V (2 * lg m - L) :=
  Summable.of_norm_bounded (summable_absf_V hE hS L) (fun m => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (V_nonneg _)])

/-- `Σ f(m) V(2 lg m − L) = ∫ g(u) H((u+L)/2) du`. -/
theorem Dsum_eq_integral (L : ℝ) :
    ∑' m : ℕ, f m * V (2 * lg m - L) = ∫ u, gk u * Ht f ((u + L) / 2) := by
  unfold V
  set F : ℕ → ℝ → ℝ := fun n u => f n * (Ioi (2 * lg n - L)).indicator gk u with hF
  have hint : ∀ n, Integrable (F n) := fun n =>
    ((integrable_gk.indicator measurableSet_Ioi).const_mul _)
  have hnorm : ∀ n, ∫ u, ‖F n u‖ = |f n| * ∫ u in Ioi (2 * lg n - L), gk u := by
    intro n
    have : ∀ u, ‖F n u‖ = |f n| * (Ioi (2 * lg n - L)).indicator gk u := fun u => by
      rw [Real.norm_eq_abs, hF, abs_mul, abs_of_nonneg (indicator_nonneg (fun x _ => (gk_pos x).le) _)]
    simp_rw [this]
    rw [integral_const_mul, integral_indicator measurableSet_Ioi]
  have hsum : Summable fun n => ∫ u, ‖F n u‖ := by
    simp_rw [hnorm]; exact summable_absf_V hE hS L
  have hswap := integral_tsum_of_summable_integral_norm hint hsum
  have hl : ∀ n, ∫ u, F n u = f n * ∫ u in Ioi (2 * lg n - L), gk u := by
    intro n; simp only [hF]; rw [integral_const_mul, integral_indicator measurableSet_Ioi]
  simp_rw [hl] at hswap
  rw [hswap]
  congr 1; funext u
  have hpt : ∀ n, F n u = if n < kc ((u + L) / 2) then f n * gk u else 0 := by
    intro n
    simp only [hF]
    by_cases h : n < kc ((u + L) / 2)
    · rw [if_pos h, indicator_of_mem]
      rw [mem_Ioi]; have := (lt_kc_iff n _).mp h; linarith
    · rw [if_neg h, indicator_of_notMem, mul_zero]
      rw [mem_Ioi, not_lt]; have := (lt_kc_iff n _).not.mp h; push Not at this; linarith
  simp_rw [hpt]
  rw [tsum_eq_sum (s := Finset.range (kc ((u + L) / 2))) (fun n hn => by
    rw [if_neg]; simpa using hn)]
  rw [Finset.sum_ite_of_true (fun n hn => Finset.mem_range.mp hn), ← Finset.sum_mul]
  unfold Ht Sp
  rw [mul_comm]

/-- **The smoothed asymptotic.** -/
theorem abs_Dsum_sub_le (L : ℝ) :
    |∑' m : ℕ, f m * V (2 * lg m - L) - c * L - 2 * K| ≤
      ADD * (E + 2 * |c| + |K|) * ((1 + |L|) * Real.exp (-L / 10)) := by
  set Z := E + 2 * |c| + |K| with hZ
  have hZ0 : 0 ≤ Z := by positivity
  have hADD : 0 ≤ ADD := integral_nonneg fun u => by have := gk_pos u; positivity
  rw [Dsum_eq_integral hE hS]
  have hmain : ∫ u, gk u * (c * ((u + L) / 2) + K) = c * L + 2 * K := by
    have : (fun u => gk u * (c * ((u + L) / 2) + K)) =
        fun u => (c / 2) * (u * gk u) + (c * L / 2 + K) * gk u := by funext u; ring
    rw [this, integral_add (integrable_mul_gk.const_mul _) (integrable_gk.const_mul _),
      integral_const_mul, integral_const_mul, integral_mul_gk_zero, integral_gk]
    ring
  have hmeas : Measurable fun u : ℝ => Ht f ((u + L) / 2) := by
    unfold Ht kc
    refine (measurable_from_nat (f := Sp f)).comp ?_
    exact Nat.measurable_ceil.comp (by fun_prop)
  have hgH : Integrable fun u => gk u * Ht f ((u + L) / 2) := by
    have hb : Integrable fun u : ℝ => 3 * Z * (1 + |L|) * gk u + 3 * Z * (|u| * gk u) := by
      refine (integrable_gk.const_mul _).add (Integrable.const_mul ?_ _)
      refine integrable_mul_gk.norm.congr (Eventually.of_forall fun u => ?_)
      simp [Real.norm_eq_abs, abs_mul, abs_of_pos (gk_pos u)]
    refine hb.mono' (continuous_gk.measurable.mul hmeas).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (gk_pos u)]
    have h1 := abs_Ht_le hE hS ((u + L) / 2)
    have h2 : |(u + L) / 2| ≤ |L| + |u| := by
      rw [abs_div, abs_two]
      have := abs_add_le u L
      have := abs_nonneg u; have := abs_nonneg L
      linarith
    have := gk_pos u
    have h3 : |Ht f ((u + L) / 2)| ≤ 3 * Z * (1 + |L|) + 3 * Z * |u| := by nlinarith
    nlinarith
  have haff : Integrable fun u => gk u * (c * ((u + L) / 2) + K) := by
    have : (fun u => gk u * (c * ((u + L) / 2) + K)) =
        fun u => (c / 2) * (u * gk u) + (c * L / 2 + K) * gk u := by funext u; ring
    rw [this]; exact (integrable_mul_gk.const_mul _).add (integrable_gk.const_mul _)
  have hdiff : (∫ u, gk u * Ht f ((u + L) / 2)) - c * L - 2 * K =
      ∫ u, gk u * (Ht f ((u + L) / 2) - c * ((u + L) / 2) - K) := by
    rw [sub_sub, ← hmain, ← integral_sub hgH haff]
    congr 1; funext u; ring
  rw [hdiff, ← Real.norm_eq_abs]
  have hbd : Integrable fun u : ℝ => Z * (1 + |L|) * Real.exp (-L / 10) *
      (gk u * (2 + |u|) * Real.exp (-u / 10)) := bound_fun_integrable_D.const_mul _
  refine (norm_integral_le_of_norm_le hbd (Eventually.of_forall fun u => ?_)).trans (le_of_eq ?_)
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (gk_pos u)]
    have h := abs_Ht_sub_le hE hS ((u + L) / 2)
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
    calc gk u * |Ht f ((u + L) / 2) - c * ((u + L) / 2) - K|
        ≤ gk u * (Z * (2 + |(u + L) / 2|) * (Real.exp (-L / 10) * Real.exp (-u / 10))) := by gcongr
      _ ≤ gk u * (Z * ((1 + |L|) * (2 + |u|)) * (Real.exp (-L / 10) * Real.exp (-u / 10))) := by
          gcongr
      _ = _ := by ring
  · rw [integral_const_mul]; unfold ADD; ring

end

end RamanujanTau.HafnerBridge2
