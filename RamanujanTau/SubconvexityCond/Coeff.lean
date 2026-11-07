/-
# The Riesz weight `g_X(n) = n^{−1/2} (1 − n/X)₊³` satisfies the `GBound` hypotheses

* `gBound_gX`: `GBound (g_X) 4 ⌊X⌋₊`;
* `gBound_gX_log`: `GBound (g_X · log) (4 log(X+1) + 4) ⌊X⌋₊`;
* `dpoly_bsm_eq`: the repo's smoothed Dirichlet polynomial `dpoly (bsm 6 X) ⌊X⌋₊` (the one in
  `MeanSquare.approx_tauL`) is `rpoly (λ · g_X) ⌊X⌋₊`.
-/
import RamanujanTau.SubconvexityCond.OffDiag

set_option autoImplicit false

namespace RamanujanTau.SubconvexityCond

open Real Finset
open RamanujanTau.RankinError RamanujanTau.MeanSquare

lemma GBound.mono {g : ℕ → ℝ} {K K' : ℝ} {N : ℕ} (hg : GBound g K N) (hK : K ≤ K') :
    GBound g K' N where
  nonneg := hg.nonneg.trans hK
  size n hn := (hg.size n hn).trans (div_le_div_of_nonneg_right hK (Real.sqrt_nonneg _))
  diff n hn := (hg.diff n hn).trans (div_le_div_of_nonneg_right hK (by positivity))
  vanish := hg.vanish

/-- The Riesz weight `g_X(n) = (1 − n/X)₊³ / √n`. -/
noncomputable def gX (X : ℝ) (n : ℕ) : ℝ := phi 3 (n / X) / Real.sqrt n

lemma phi3_le_one {u : ℝ} (hu : 0 ≤ u) : phi 3 u ≤ 1 := by
  unfold phi
  exact pow_le_one₀ (le_max_right _ _) (max_le (by linarith) zero_le_one)

lemma phi3_lip {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) : |phi 3 u - phi 3 v| ≤ 3 * |u - v| := by
  unfold phi
  set a := max (1 - u) 0
  set b := max (1 - v) 0
  have ha0 : 0 ≤ a := le_max_right _ _
  have hb0 : 0 ≤ b := le_max_right _ _
  have ha1 : a ≤ 1 := max_le (by linarith) zero_le_one
  have hb1 : b ≤ 1 := max_le (by linarith) zero_le_one
  have hab : |a - b| ≤ |u - v| := by
    have := abs_max_sub_max_le_abs (1 - u) (1 - v) 0
    rw [show (1 - u) - (1 - v) = -(u - v) by ring, abs_neg] at this; exact this
  have e : a ^ 3 - b ^ 3 = (a - b) * (a ^ 2 + a * b + b ^ 2) := by ring
  rw [e, abs_mul]
  have h3 : |a ^ 2 + a * b + b ^ 2| ≤ 3 := by
    rw [abs_of_nonneg (by positivity)]; nlinarith [mul_le_mul ha1 hb1 hb0 zero_le_one]
  calc |a - b| * |a ^ 2 + a * b + b ^ 2| ≤ |u - v| * 3 :=
        mul_le_mul hab h3 (abs_nonneg _) (abs_nonneg _)
    _ = 3 * |u - v| := by ring

lemma gX_vanish {X : ℝ} (hX : 0 < X) {n : ℕ} (hn : ⌊X⌋₊ < n) : gX X n = 0 := by
  have h1 : X < n := by
    have := Nat.lt_floor_add_one X
    have : ((⌊X⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at this; linarith
  rw [gX, phi_of_gt (by norm_num) ((one_lt_div hX).2 h1), zero_div]

lemma inv_sqrt_sub_le {n : ℕ} (hn : 1 ≤ n) :
    |1 / Real.sqrt n - 1 / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ 1 / (n * Real.sqrt n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set s := Real.sqrt n
  set r := Real.sqrt ((n + 1 : ℕ) : ℝ)
  have hs0 : 0 < s := Real.sqrt_pos.2 hn0
  have hss : s * s = n := Real.mul_self_sqrt hn0.le
  have hrr : r * r = n + 1 := by rw [Real.mul_self_sqrt (by positivity)]; push_cast; ring
  have hsr : s ≤ r := Real.sqrt_le_sqrt (by push_cast; linarith)
  have hr0 : 0 < r := hs0.trans_le hsr
  have hpos : 0 ≤ 1 / s - 1 / r := by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le hs0 hsr
  rw [abs_of_nonneg hpos, ← hss, div_sub_div _ _ hs0.ne' hr0.ne',
    div_le_div_iff₀ (by positivity) (by positivity)]
  -- `(r − s) s³ ≤ r s` from `(r − s)(r + s) = 1`
  have hrs : (r - s) * (r + s) = 1 := by nlinarith
  have h1 : (r - s) * (s * s) ≤ s := by
    have : (r - s) * (s * s) ≤ (r - s) * ((r + s) * s) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
    calc (r - s) * (s * s) ≤ (r - s) * ((r + s) * s) := this
      _ = s := by rw [← mul_assoc, hrs, one_mul]
  nlinarith

/-- **`g_X` satisfies `GBound` with `K = 4`.** -/
theorem gBound_gX {X : ℝ} (hX : 1 ≤ X) : GBound (gX X) 4 ⌊X⌋₊ where
  nonneg := by norm_num
  size n hn := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [gX, abs_div, abs_of_nonneg (phi_nonneg _ _), abs_of_nonneg (Real.sqrt_nonneg _)]
    refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    linarith [phi3_le_one (u := n / X) (div_nonneg (Nat.cast_nonneg _) (by linarith))]
  diff n hn := by
    have hX0 : 0 < X := by linarith
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
    set p0 := phi 3 (n / X)
    set p1 := phi 3 (((n + 1 : ℕ) : ℝ) / X)
    have e : gX X n - gX X (n + 1) =
        p0 * (1 / Real.sqrt n - 1 / Real.sqrt ((n + 1 : ℕ) : ℝ)) +
          (p0 - p1) * (1 / Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
      simp only [gX, p0, p1]; ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have t1 : |p0 * (1 / Real.sqrt n - 1 / Real.sqrt ((n + 1 : ℕ) : ℝ))| ≤ 1 / (n * Real.sqrt n) := by
      rw [abs_mul, abs_of_nonneg (phi_nonneg _ _)]
      have := inv_sqrt_sub_le hn
      have hp := phi3_le_one (u := n / X) (div_nonneg (Nat.cast_nonneg _) hX0.le)
      calc p0 * |1 / Real.sqrt n - 1 / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤
          1 * (1 / (n * Real.sqrt n)) := mul_le_mul hp this (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    have t2 : |(p0 - p1) * (1 / Real.sqrt ((n + 1 : ℕ) : ℝ))| ≤ 3 / (n * Real.sqrt n) := by
      rcases le_or_gt (n : ℝ) X with hnX | hnX
      · have hl : |p0 - p1| ≤ 3 * |(n : ℝ) / X - ((n + 1 : ℕ) : ℝ) / X| := phi3_lip
          (div_nonneg (Nat.cast_nonneg _) hX0.le) (div_nonneg (Nat.cast_nonneg _) hX0.le)
        have e2 : (n : ℝ) / X - ((n + 1 : ℕ) : ℝ) / X = -(1 / X) := by push_cast; ring
        rw [e2, abs_neg, abs_of_pos (show 0 < 1 / X by positivity)] at hl
        rw [abs_mul, abs_of_pos (show 0 < 1 / Real.sqrt ((n + 1 : ℕ) : ℝ) by positivity)]
        have hsq : Real.sqrt n ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) :=
          Real.sqrt_le_sqrt (by push_cast; linarith)
        have h1 : 1 / Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ 1 / Real.sqrt n :=
          one_div_le_one_div_of_le hs0 hsq
        have h2 : 3 * (1 / X) ≤ 3 / n := by
          rw [mul_one_div]; exact div_le_div_of_nonneg_left (by norm_num) hn0 hnX
        calc |p0 - p1| * (1 / Real.sqrt ((n + 1 : ℕ) : ℝ)) ≤ (3 / n) * (1 / Real.sqrt n) :=
              mul_le_mul (hl.trans h2) h1 (by positivity) (by positivity)
          _ = 3 / (n * Real.sqrt n) := by field_simp
      · have h0 : p0 = 0 := phi_of_gt (by norm_num) ((one_lt_div hX0).2 hnX)
        have h1 : p1 = 0 := phi_of_gt (by norm_num) ((one_lt_div hX0).2 (by push_cast; linarith))
        rw [h0, h1]; simp; positivity
    have : (4 : ℝ) / (n * Real.sqrt n) = 1 / (n * Real.sqrt n) + 3 / (n * Real.sqrt n) := by ring
    linarith
  vanish n hn := gX_vanish (by linarith) hn

/-- **`g_X · log` satisfies `GBound` with `K = 4 log(X+1) + 4`.** -/
theorem gBound_gX_log {X : ℝ} (hX : 1 ≤ X) :
    GBound (fun n => gX X n * Real.log n) (4 * Real.log (X + 1) + 4) ⌊X⌋₊ := by
  have hg := gBound_gX hX
  have hX0 : 0 < X := by linarith
  have hlX : 0 ≤ Real.log (X + 1) := Real.log_nonneg (by linarith)
  refine ⟨by positivity, fun n hn => ?_, fun n hn => ?_, fun n hn => ?_⟩
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rcases le_or_gt n ⌊X⌋₊ with hnN | hnN
    · have hnX : (n : ℝ) ≤ X := (Nat.le_floor_iff hX0.le).1 hnN
      have hl0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
      have hl : Real.log n ≤ Real.log (X + 1) := Real.log_le_log hn0 (by linarith)
      rw [abs_mul, abs_of_nonneg hl0]
      have := hg.size n hn
      calc |gX X n| * Real.log n ≤ (4 / Real.sqrt n) * Real.log (X + 1) :=
            mul_le_mul this hl hl0 (by positivity)
        _ ≤ (4 * Real.log (X + 1) + 4) / Real.sqrt n := by
            rw [div_mul_eq_mul_div]
            exact div_le_div_of_nonneg_right (by nlinarith) (Real.sqrt_nonneg _)
    · rw [hg.vanish n hnN, zero_mul, abs_zero]; positivity
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rcases le_or_gt n ⌊X⌋₊ with hnN | hnN
    · have hnX : (n : ℝ) ≤ X := (Nat.le_floor_iff hX0.le).1 hnN
      have e : gX X n * Real.log n - gX X (n + 1) * Real.log ((n + 1 : ℕ) : ℝ) =
          (gX X n - gX X (n + 1)) * Real.log ((n + 1 : ℕ) : ℝ) -
            gX X n * (Real.log ((n + 1 : ℕ) : ℝ) - Real.log n) := by ring
      rw [e]
      refine (abs_sub _ _).trans ?_
      have hl0 : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) := Real.log_nonneg (by push_cast; linarith)
      have hl : Real.log ((n + 1 : ℕ) : ℝ) ≤ Real.log (X + 1) :=
        Real.log_le_log (by positivity) (by push_cast; linarith)
      have hd0 : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) - Real.log n := by
        rw [sub_nonneg]; exact Real.log_le_log hn0 (by push_cast; linarith)
      have hd : Real.log ((n + 1 : ℕ) : ℝ) - Real.log n ≤ 1 / n := by
        rw [← Real.log_div (by positivity) hn0.ne']
        refine (Real.log_le_sub_one_of_pos (by positivity)).trans (le_of_eq ?_)
        push_cast; field_simp; ring
      have t1 : |(gX X n - gX X (n + 1)) * Real.log ((n + 1 : ℕ) : ℝ)| ≤
          4 / (n * Real.sqrt n) * Real.log (X + 1) := by
        rw [abs_mul, abs_of_nonneg hl0]
        exact mul_le_mul (hg.diff n hn) hl hl0 (by positivity)
      have t2 : |gX X n * (Real.log ((n + 1 : ℕ) : ℝ) - Real.log n)| ≤
          4 / (n * Real.sqrt n) := by
        rw [abs_mul, abs_of_nonneg hd0]
        calc |gX X n| * (Real.log ((n + 1 : ℕ) : ℝ) - Real.log n) ≤
            (4 / Real.sqrt n) * (1 / n) := mul_le_mul (hg.size n hn) hd hd0 (by positivity)
          _ = 4 / (n * Real.sqrt n) := by field_simp
      have : (4 * Real.log (X + 1) + 4) / (n * Real.sqrt n) =
          4 / (n * Real.sqrt n) * Real.log (X + 1) + 4 / (n * Real.sqrt n) := by ring
      linarith
    · rw [hg.vanish n hnN, hg.vanish (n + 1) (by omega)]; simp; positivity
  · rw [hg.vanish n hn, zero_mul]

/-- The repo's smoothed polynomial is `rpoly (λ · g_X)`. -/
lemma dpoly_bsm_eq (X : ℝ) (N : ℕ) (t : ℝ) :
    dpoly (bsm 6 X) N t = rpoly (fun n => lam n * gX X n) N t := by
  unfold rpoly
  congr 1
  funext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [bsm, lam, tau_zero]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have e : (n : ℝ) ^ (-(6 : ℝ)) = (n : ℝ) ^ (-(11 / 2 : ℝ)) / Real.sqrt n := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hn0]; norm_num
  simp only [bsm, lam, gX, e]
  push_cast
  ring

end RamanujanTau.SubconvexityCond
