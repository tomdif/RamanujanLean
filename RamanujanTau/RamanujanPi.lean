/-
# A Ramanujan series for `1/π`

  `Σ_{n≥0} (−1)ⁿ (6n+1) ((1/2)_n)³ / (n!³ 8ⁿ) = 2√2/π`.

Proof by a one-parameter deformation and Wallis' product (no modular forms):
* `F(k,n) = (6n+4k+1)(1/2)_n² (1/2+2k)_n / (n! (1+k)_n² (−8)ⁿ)` has `F(0,n)` = the summand;
* the certificate `G(k,n) = 4 r_k n/(6n+4k+1) · F(k,n)`, `r_k = 16(k+1)²/((4k+1)(4k+3))`, satisfies
  `F(k+1,n) − r_k F(k,n) = G(k,n+1) − G(k,n)`, so `S(k+1) = r_k S(k)` for `S(k) = Σ_n F(k,n)`;
* `S(k) = (4k+1)(1 + O(1/k))` since the `n ≥ 1` terms are `O(4⁻ⁿ/k)`;
* `((4k+1)/∏_{i<k} r_i)² = (4k+1)/((2k+1) W_{2k} W_k) → 8/π²` with Wallis' `W_k → π/2`.
-/
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

namespace RamanujanPi
open Real Finset Filter
open scoped Topology Nat

/-- the rising factorial `(a)_n`. -/
noncomputable def ph (a : ℝ) (n : ℕ) : ℝ := ∏ i ∈ range n, (a + i)

lemma ph_zero (a : ℝ) : ph a 0 = 1 := by simp [ph]

lemma ph_succ (a : ℝ) (n : ℕ) : ph a (n + 1) = ph a n * (a + n) := by simp [ph, prod_range_succ]

lemma ph_shift (a : ℝ) (n : ℕ) : ph a (n + 1) = a * ph (a + 1) n := by
  induction n with
  | zero => simp [ph]
  | succ n ih =>
    rw [ph_succ, ih, ph_succ]; push_cast; ring

lemma ph_pos {a : ℝ} (ha : 0 < a) (n : ℕ) : 0 < ph a n :=
  prod_pos fun i _ => by positivity

lemma ph_one (n : ℕ) : ph 1 n = n ! := by
  induction n with
  | zero => simp [ph]
  | succ n ih => rw [ph_succ, ih, Nat.factorial_succ]; push_cast; ring

/-- `(a)_n ≤ (b)_n` for `0 < a ≤ b`. -/
lemma ph_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (n : ℕ) : ph a n ≤ ph b n :=
  prod_le_prod (fun i _ => by positivity) fun i _ => by linarith

/-! ### the deformation and the certificate -/

noncomputable def r (k : ℕ) : ℝ := 16 * ((k : ℝ) + 1) ^ 2 / ((4 * k + 1) * (4 * k + 3))

noncomputable def F (k n : ℕ) : ℝ :=
  (6 * n + 4 * k + 1) * ph (1 / 2) n ^ 2 * ph (1 / 2 + 2 * k) n / (n ! * ph (1 + k) n ^ 2 * (-8) ^ n)

noncomputable def G (k n : ℕ) : ℝ :=
  4 * r k * n * ph (1 / 2) n ^ 2 * ph (1 / 2 + 2 * k) n / (n ! * ph (1 + k) n ^ 2 * (-8) ^ n)

lemma cert (k n : ℕ) : F (k + 1) n - r k * F k n = G k (n + 1) - G k n := by
  -- express the shifted rising factorials through the base ones
  set a : ℝ := 1 / 2 + 2 * k with ha
  have ha0 : 0 < a := by positivity
  have e1 : ph (1 / 2 + 2 * ((k + 1 : ℕ) : ℝ)) n * (a * (a + 1)) = ph a n * ((a + n) * (a + 1 + n)) := by
    have h1 : ph a (n + 2) = ph a n * (a + n) * (a + ((n + 1 : ℕ) : ℝ)) := by rw [ph_succ, ph_succ]
    have h2 : ph a (n + 2) = a * ((a + 1) * ph (a + 1 + 1) n) := by rw [ph_shift, ph_shift]
    have : (1 / 2 + 2 * ((k + 1 : ℕ) : ℝ)) = a + 1 + 1 := by rw [ha]; push_cast; ring
    rw [this]
    push_cast at h1
    linear_combination h1 - h2
  have e2 : ph (1 + ((k + 1 : ℕ) : ℝ)) n * (1 + k) = ph (1 + k) n * (1 + k + n) := by
    have h := ph_shift (1 + k) n
    rw [ph_succ] at h
    have : (1 + ((k + 1 : ℕ) : ℝ)) = 1 + k + 1 := by push_cast; ring
    rw [this]; linear_combination -h
  have hB := ph_pos ha0 n
  have hQ := ph_pos (show (0 : ℝ) < 1 + k by positivity) n
  have hA := ph_pos (show (0 : ℝ) < 1 / 2 by norm_num) n
  have hB' : ph (1 / 2 + 2 * ((k + 1 : ℕ) : ℝ)) n = ph a n * ((a + n) * (a + 1 + n)) / (a * (a + 1)) := by
    rw [eq_div_iff (by positivity)]; exact e1
  have hQ' : ph (1 + ((k + 1 : ℕ) : ℝ)) n = ph (1 + k) n * (1 + k + n) / (1 + k) := by
    rw [eq_div_iff (by positivity)]; exact e2
  simp only [F, G, r, hB', hQ', ph_succ, Nat.factorial_succ, pow_succ]
  rw [← ha]
  have hf : (0 : ℝ) < n ! := by exact_mod_cast n.factorial_pos
  have h8 : ((-8 : ℝ)) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hk1 : (0 : ℝ) < 1 + k + n := by positivity
  have hk2 : (0 : ℝ) < 4 * k + 1 := by positivity
  have hk3 : (0 : ℝ) < 4 * k + 3 := by positivity
  push_cast
  rw [ha]
  field_simp
  ring

/-! ### bounds and convergence -/

lemma ph_half_le_fact (n : ℕ) : ph (1 / 2) n ≤ n ! := by
  rw [← ph_one]; exact ph_le (by norm_num) (by norm_num) n

lemma ph_le_two_pow (k n : ℕ) : ph (1 / 2 + 2 * k) n ≤ 2 ^ n * ph (1 + k) n := by
  rw [ph, ph, show (2 : ℝ) ^ n = ∏ _i ∈ range n, (2 : ℝ) by simp, ← prod_mul_distrib]
  exact prod_le_prod (fun i _ => by positivity) fun i _ => by linarith

lemma ph_half_le_shift (k n : ℕ) : ph (1 / 2) (n + 1) ≤ ph (1 + k) (n + 1) / (2 * (k + 1)) := by
  rw [ph_shift, ph_shift (1 + (k : ℝ)), le_div_iff₀ (by positivity)]
  have := ph_le (show (0 : ℝ) < 1 / 2 + 1 by norm_num) (show (1 / 2 + 1 : ℝ) ≤ 1 + k + 1 by
    have := k.cast_nonneg (α := ℝ); linarith) n
  have h0 := ph_pos (show (0 : ℝ) < 1 / 2 + 1 by norm_num) n
  nlinarith

lemma abs_F (k n : ℕ) : |F k n| = (6 * n + 4 * k + 1) * ph (1 / 2) n ^ 2 * ph (1 / 2 + 2 * k) n
    / (n ! * ph (1 + k) n ^ 2 * 8 ^ n) := by
  have hA := ph_pos (show (0 : ℝ) < 1 / 2 by norm_num) n
  have hB := ph_pos (show (0 : ℝ) < 1 / 2 + 2 * k by positivity) n
  have hQ := ph_pos (show (0 : ℝ) < 1 + k by positivity) n
  have hf : (0 : ℝ) < n ! := by exact_mod_cast n.factorial_pos
  rw [F]
  simp only [abs_div, abs_mul, abs_pow, abs_neg, abs_of_pos hA, abs_of_pos hB,
    abs_of_pos hQ, abs_of_pos hf, abs_of_pos (by positivity : (0 : ℝ) < 6 * n + 4 * k + 1)]
  norm_num

lemma F_bound (k n : ℕ) : |F k n| ≤ (6 * n + 4 * k + 1) * (1 / 4) ^ n := by
  have hA := ph_pos (show (0 : ℝ) < 1 / 2 by norm_num) n
  have hB := ph_pos (show (0 : ℝ) < 1 / 2 + 2 * k by positivity) n
  have hQ := ph_pos (show (0 : ℝ) < 1 + k by positivity) n
  have hf : (0 : ℝ) < n ! := by exact_mod_cast n.factorial_pos
  have h1 := ph_half_le_fact n
  have h2 := ph_le (show (0 : ℝ) < 1 / 2 by norm_num) (show (1 / 2 : ℝ) ≤ 1 + k by
    have := k.cast_nonneg (α := ℝ); linarith) n
  have h3 := ph_le_two_pow k n
  rw [abs_F, div_le_iff₀ (by positivity)]
  have e : (6 * n + 4 * k + 1) * (1 / 4 : ℝ) ^ n * (n ! * ph (1 + k) n ^ 2 * 8 ^ n)
      = (6 * n + 4 * k + 1) * (n ! * ph (1 + k) n * (2 ^ n * ph (1 + k) n)) := by
    rw [show (8 : ℝ) ^ n = 4 ^ n * 2 ^ n by rw [← mul_pow]; norm_num]
    field_simp
    rw [← mul_pow]; norm_num
  rw [e]
  have key : ph (1 / 2) n ^ 2 * ph (1 / 2 + 2 * k) n ≤ n ! * ph (1 + k) n * (2 ^ n * ph (1 + k) n) := by
    calc ph (1 / 2) n ^ 2 * ph (1 / 2 + 2 * k) n = ph (1 / 2) n * ph (1 / 2) n * ph (1 / 2 + 2 * k) n := by ring
      _ ≤ n ! * ph (1 + k) n * (2 ^ n * ph (1 + k) n) := by gcongr
  rw [mul_assoc (6 * (n : ℝ) + 4 * k + 1)]
  exact mul_le_mul_of_nonneg_left key (by positivity)

lemma F_bound_succ (k n : ℕ) : |F k (n + 1)| ≤ (3 * (n + 1) + 2) * (1 / 4) ^ (n + 1) := by
  have hA := ph_pos (show (0 : ℝ) < 1 / 2 by norm_num) (n + 1)
  have hB := ph_pos (show (0 : ℝ) < 1 / 2 + 2 * k by positivity) (n + 1)
  have hQ := ph_pos (show (0 : ℝ) < 1 + k by positivity) (n + 1)
  have hf : (0 : ℝ) < (n + 1)! := by exact_mod_cast (n + 1).factorial_pos
  have h1 := ph_half_le_fact (n + 1)
  have h2 := ph_half_le_shift k n
  have h3 := ph_le_two_pow k (n + 1)
  rw [abs_F, div_le_iff₀ (by positivity)]
  have hk : (0 : ℝ) < 2 * (k + 1) := by positivity
  have hc : ((6 * ((n + 1 : ℕ) : ℝ) + 4 * k + 1) / (2 * (k + 1))) ≤ 3 * (n + 1) + 2 := by
    rw [div_le_iff₀ hk]; push_cast; nlinarith [k.cast_nonneg (α := ℝ), n.cast_nonneg (α := ℝ)]
  have e : (3 * (n + 1) + 2) * (1 / 4 : ℝ) ^ (n + 1) * ((n + 1)! * ph (1 + k) (n + 1) ^ 2 * 8 ^ (n + 1))
      = (3 * (n + 1) + 2) * ((n + 1)! * ph (1 + k) (n + 1) * (2 ^ (n + 1) * ph (1 + k) (n + 1))) := by
    rw [show (8 : ℝ) ^ (n + 1) = 4 ^ (n + 1) * 2 ^ (n + 1) by rw [← mul_pow]; norm_num]
    field_simp
    rw [← mul_pow]; norm_num
  rw [e]
  calc (6 * ((n + 1 : ℕ) : ℝ) + 4 * k + 1) * ph (1 / 2) (n + 1) ^ 2 * ph (1 / 2 + 2 * k) (n + 1)
      = ((6 * ((n + 1 : ℕ) : ℝ) + 4 * k + 1) / (2 * (k + 1))) * ph (1 / 2) (n + 1)
          * ((2 * (k + 1)) * ph (1 / 2) (n + 1)) * ph (1 / 2 + 2 * k) (n + 1) := by field_simp
    _ ≤ (3 * (n + 1) + 2) * (n + 1)! * ph (1 + k) (n + 1) * (2 ^ (n + 1) * ph (1 + k) (n + 1)) := by
        have h2' : (2 * (k + 1)) * ph (1 / 2) (n + 1) ≤ ph (1 + k) (n + 1) := by
          rw [le_div_iff₀ hk] at h2; linarith
        gcongr
    _ = _ := by ring

lemma summable_bound (c : ℝ) : Summable fun n : ℕ => (6 * n + c) * (1 / 4 : ℝ) ^ n := by
  have h1 : Summable fun n : ℕ => (n : ℝ) * (1 / 4 : ℝ) ^ n :=
    (summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)).congr fun n => by simp
  have h2 := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)
  exact ((h1.mul_left 6).add (h2.mul_left c)).congr fun n => by ring

lemma summable_F (k : ℕ) : Summable (F k) :=
  Summable.of_norm_bounded (summable_bound (4 * k + 1)) fun n => by
    rw [Real.norm_eq_abs]; simpa [add_assoc] using F_bound k n

noncomputable def S (k : ℕ) : ℝ := ∑' n, F k n

/-! ### the recursion `S(k+1) = r_k S(k)` -/

lemma G_zero (k : ℕ) : G k 0 = 0 := by simp [G]

lemma G_tendsto (k : ℕ) : Tendsto (G k) atTop (𝓝 0) := by
  have hb : ∀ n, |G k n| ≤ 4 * r k * (n * (1 / 4 : ℝ) ^ n) := fun n => by
    have hr : 0 < r k := by unfold r; positivity
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [G_zero]
    have hF := F_bound k n
    have hpos : (0 : ℝ) < 6 * n + 4 * k + 1 := by positivity
    have : G k n = 4 * r k * n / (6 * n + 4 * k + 1) * F k n := by
      rw [G, F]; field_simp
    rw [this, abs_mul, abs_div, abs_of_pos hpos, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * r k * n)]
    calc 4 * r k * n / (6 * n + 4 * k + 1) * |F k n| ≤ 4 * r k * n / (6 * n + 4 * k + 1) *
          ((6 * n + 4 * k + 1) * (1 / 4) ^ n) := by gcongr
      _ = _ := by field_simp
  have ht : Tendsto (fun n : ℕ => 4 * r k * ((n : ℝ) * (1 / 4 : ℝ) ^ n)) atTop (𝓝 0) := by
    simpa using (tendsto_self_mul_const_pow_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)).const_mul
      (4 * r k)
  exact squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact hb n) ht

theorem S_succ (k : ℕ) : S (k + 1) = r k * S k := by
  have hs := ((summable_F (k + 1)).hasSum.sub ((summable_F k).hasSum.mul_left (r k)))
  have h1 := hs.tendsto_sum_nat
  have h2 : (fun N => ∑ n ∈ range N, (F (k + 1) n - r k * F k n)) = G k := by
    funext N
    rw [Finset.sum_congr rfl fun n _ => cert k n, Finset.sum_range_sub, G_zero, sub_zero]
  rw [h2] at h1
  have := tendsto_nhds_unique h1 (G_tendsto k)
  rw [S, S]; linarith

/-- the partial products `∏_{i<k} r_i`. -/
noncomputable def Pr (k : ℕ) : ℝ := ∏ i ∈ range k, r i

lemma r_pos (k : ℕ) : 0 < r k := by unfold r; positivity

lemma Pr_pos (k : ℕ) : 0 < Pr k := prod_pos fun i _ => r_pos i

theorem S_eq (k : ℕ) : S k = S 0 * Pr k := by
  induction k with
  | zero => simp [Pr]
  | succ k ih => rw [S_succ, ih]; simp only [Pr, prod_range_succ]; ring

/-! ### `S(k) ~ 4k+1` -/

lemma F_zero (k : ℕ) : F k 0 = 4 * k + 1 := by simp [F, ph_zero]

noncomputable def C : ℝ := ∑' n : ℕ, (3 * ((n : ℝ) + 1) + 2) * (1 / 4 : ℝ) ^ (n + 1)

lemma summable_C : Summable fun n : ℕ => (3 * ((n : ℝ) + 1) + 2) * (1 / 4 : ℝ) ^ (n + 1) := by
  have := (summable_bound 5).comp_injective (add_left_injective 1)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) this
  simp only [Function.comp, Nat.cast_add, Nat.cast_one]
  gcongr <;> norm_num

lemma tail_bound (k : ℕ) : |S k - (4 * k + 1)| ≤ C := by
  rw [S, (summable_F k).tsum_eq_zero_add, F_zero, add_sub_cancel_left]
  have hs := (summable_F k).comp_injective (add_left_injective 1)
  calc |∑' n, F k (n + 1)| ≤ ∑' n, |F k (n + 1)| := by
        simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs.norm
    _ ≤ C := Summable.tsum_le_tsum (fun n => F_bound_succ k n) hs.abs summable_C

lemma S_ratio : Tendsto (fun k : ℕ => S k / (4 * k + 1)) atTop (𝓝 1) := by
  have hd : Tendsto (fun k : ℕ => (4 * (k : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
  have h0 : Tendsto (fun k : ℕ => (S k - (4 * k + 1)) / (4 * k + 1)) atTop (𝓝 0) := by
    have hC : Tendsto (fun k : ℕ => C / (4 * (k : ℝ) + 1)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hd
    refine squeeze_zero_norm (fun k => ?_) hC
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * k + 1)]
    exact div_le_div_of_nonneg_right (tail_bound k) (by positivity)
  have := h0.const_add 1
  rw [add_zero] at this
  refine this.congr fun k => ?_
  field_simp; ring

/-! ### the Wallis limit -/

open Real.Wallis in
lemma wallis_identity (k : ℕ) : ((4 * k + 1) / Pr k) ^ 2 * ((2 * k + 1) * W (2 * k) * W k) = 4 * k + 1 := by
  induction k with
  | zero => simp [Pr, W]
  | succ k ih =>
    have hP := Pr_pos k
    have hW1 := W_pos (2 * k)
    have hW2 := W_pos k
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, W_succ, W_succ, W_succ, Pr, prod_range_succ, ← Pr]
    push_cast at ih ⊢
    have hr : r k = 16 * ((k : ℝ) + 1) ^ 2 / ((4 * k + 1) * (4 * k + 3)) := rfl
    rw [hr]
    have hk1 : (0 : ℝ) < 4 * k + 1 := by positivity
    have e : ((4 * k + 1) / Pr k) ^ 2 = (4 * k + 1) / ((2 * k + 1) * W (2 * k) * W k) := by
      rw [eq_div_iff (by positivity)]; exact ih
    have e2 : ((4 * ((k : ℝ) + 1) + 1) / (Pr k * (16 * (k + 1) ^ 2 / ((4 * k + 1) * (4 * k + 3))))) ^ 2
        = ((4 * k + 1) / Pr k) ^ 2 * ((4 * k + 5) * (4 * k + 3) / (16 * (k + 1) ^ 2)) ^ 2 := by
      field_simp; ring
    rw [e2, e]
    field_simp
    ring

open Real.Wallis in
lemma ratio_tendsto : Tendsto (fun k : ℕ => (4 * k + 1) / Pr k) atTop (𝓝 (2 * √2 / π)) := by
  have hW := tendsto_W_nhds_pi_div_two
  have hW2 : Tendsto (fun k : ℕ => W (2 * k)) atTop (𝓝 (π / 2)) :=
    hW.comp (tendsto_id.const_mul_atTop' (by norm_num))
  have hq : Tendsto (fun k : ℕ => (4 * (k : ℝ) + 1) / (2 * k + 1)) atTop (𝓝 2) := by
    have : Tendsto (fun k : ℕ => 2 - 1 / ((2 * (k : ℝ)) + 1)) atTop (𝓝 (2 - 0)) := by
      refine tendsto_const_nhds.sub ?_
      exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _
        (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)))
    rw [sub_zero] at this
    refine this.congr fun k => ?_
    field_simp; ring
  have hsq : Tendsto (fun k : ℕ => ((4 * k + 1) / Pr k) ^ 2) atTop (𝓝 (2 / (π / 2 * (π / 2)))) := by
    have := (hq.div (hW2.mul hW) (by positivity))
    refine this.congr fun k => ?_
    have h := wallis_identity k
    have hpos : 0 < (2 * (k : ℝ) + 1) * W (2 * k) * W k := by
      have := W_pos (2 * k); have := W_pos k; positivity
    show (4 * (k : ℝ) + 1) / (2 * k + 1) / (W (2 * k) * W k) = _
    rw [(eq_div_iff hpos.ne').mpr h]
    have := W_pos (2 * k); have := W_pos k
    field_simp
  have hs := hsq.sqrt
  have hval : Real.sqrt (2 / (π / 2 * (π / 2))) = 2 * √2 / π := by
    rw [show 2 / (π / 2 * (π / 2)) = (2 * √2 / π) ^ 2 by
      rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]; field_simp]
    exact Real.sqrt_sq (by positivity)
  rw [hval] at hs
  refine hs.congr fun k => ?_
  exact Real.sqrt_sq (div_pos (by positivity) (Pr_pos k)).le

/-! ### the series -/

theorem S_zero : S 0 = 2 * √2 / π := by
  have h := (ratio_tendsto.mul S_ratio)
  rw [mul_one] at h
  have hc : (fun k : ℕ => (4 * (k : ℝ) + 1) / Pr k * (S k / (4 * k + 1))) = fun _ => S 0 := by
    funext k
    rw [S_eq k]
    have := Pr_pos k
    field_simp
  rw [hc] at h
  exact tendsto_nhds_unique tendsto_const_nhds h

/-- **Ramanujan-type series for `1/π`**: `Σ (−1)ⁿ (6n+1) ((1/2)_n)³/(n!³ 8ⁿ) = 2√2/π`. -/
theorem ramanujan_pi_series :
    HasSum (fun n : ℕ => (-1) ^ n * (6 * n + 1) * ph (1 / 2) n ^ 3 / ((n ! : ℝ) ^ 3 * 8 ^ n)) (2 * √2 / π) := by
  rw [← S_zero]
  convert (summable_F 0).hasSum using 1
  funext n
  simp only [F, Nat.cast_zero, mul_zero, add_zero, ph_one]
  rw [show (-8 : ℝ) ^ n = (-1) ^ n * 8 ^ n by rw [← mul_pow]; norm_num]
  have hf : (0 : ℝ) < n ! := by exact_mod_cast n.factorial_pos
  have : ((-1 : ℝ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  field_simp
  rw [← pow_mul, show n * 2 = 2 * n by ring, pow_mul]; norm_num

/-! ## Ramanujan's first series: `Σ (6n+1)((1/2)_n)³/(n!³ 4ⁿ) = 4/π`

The same method with `F(k,n) = (6n+4k+1)(1/2)_n³/(n!(1+k)_n² 4ⁿ)`, `r_k = ((2k+2)/(2k+1))²`, certificate
`G(k,n) = 8 r_k n/(6n+4k+1) · F(k,n)`, and `∏_{i<k} r_i = (2k+1) W_k`. -/

namespace Four

noncomputable def r (k : ℕ) : ℝ := ((2 * (k : ℝ) + 2) / (2 * k + 1)) ^ 2

noncomputable def F (k n : ℕ) : ℝ := (6 * n + 4 * k + 1) * ph (1 / 2) n ^ 3 / (n ! * ph (1 + k) n ^ 2 * 4 ^ n)

noncomputable def G (k n : ℕ) : ℝ := 8 * r k * n * ph (1 / 2) n ^ 3 / (n ! * ph (1 + k) n ^ 2 * 4 ^ n)

lemma cert (k n : ℕ) : F (k + 1) n - r k * F k n = G k (n + 1) - G k n := by
  have e2 : ph (1 + ((k + 1 : ℕ) : ℝ)) n * (1 + k) = ph (1 + k) n * (1 + k + n) := by
    have h := ph_shift (1 + k) n
    rw [ph_succ] at h
    have : (1 + ((k + 1 : ℕ) : ℝ)) = 1 + k + 1 := by push_cast; ring
    rw [this]; linear_combination -h
  have hQ := ph_pos (show (0 : ℝ) < 1 + k by positivity) n
  have hA := ph_pos (show (0 : ℝ) < 1 / 2 by norm_num) n
  have hQ' : ph (1 + ((k + 1 : ℕ) : ℝ)) n = ph (1 + k) n * (1 + k + n) / (1 + k) := by
    rw [eq_div_iff (by positivity)]; exact e2
  simp only [F, G, r, hQ', ph_succ, Nat.factorial_succ, pow_succ]
  have hf : (0 : ℝ) < n ! := by exact_mod_cast n.factorial_pos
  have hk1 : (0 : ℝ) < 1 + k + n := by positivity
  have hk2 : (0 : ℝ) < 2 * k + 1 := by positivity
  push_cast
  field_simp
  ring

lemma abs_F (k n : ℕ) : |F k n| = F k n := abs_of_nonneg (by
  have := ph_pos (show (0 : ℝ) < 1 / 2 by norm_num) n
  have := ph_pos (show (0 : ℝ) < 1 + k by positivity) n
  unfold F; positivity)

lemma F_le (k n : ℕ) (c : ℝ) (hc : ph (1 / 2) n ≤ c * ph (1 + k) n) (hc0 : 0 ≤ c) :
    F k n ≤ (6 * n + 4 * k + 1) * c * (1 / 4) ^ n := by
  have hA := ph_pos (show (0 : ℝ) < 1 / 2 by norm_num) n
  have hQ := ph_pos (show (0 : ℝ) < 1 + k by positivity) n
  have hf : (0 : ℝ) < n ! := by exact_mod_cast n.factorial_pos
  have h1 := ph_half_le_fact n
  have h2 := ph_le (show (0 : ℝ) < 1 / 2 by norm_num) (show (1 / 2 : ℝ) ≤ 1 + k by
    have := k.cast_nonneg (α := ℝ); linarith) n
  rw [F, div_le_iff₀ (by positivity)]
  have e : (6 * n + 4 * k + 1) * c * (1 / 4 : ℝ) ^ n * (n ! * ph (1 + k) n ^ 2 * 4 ^ n)
      = (6 * n + 4 * k + 1) * (n ! * ph (1 + k) n * (c * ph (1 + k) n)) := by
    have h4 : (1 / 4 : ℝ) ^ n * 4 ^ n = 1 := by rw [← mul_pow]; norm_num
    linear_combination ((6 * n + 4 * k + 1) * c * n ! * ph (1 + k) n ^ 2) * h4
  rw [e]
  have key : ph (1 / 2) n ^ 3 ≤ n ! * ph (1 + k) n * (c * ph (1 + k) n) := by
    calc ph (1 / 2) n ^ 3 = ph (1 / 2) n * ph (1 / 2) n * ph (1 / 2) n := by ring
      _ ≤ n ! * ph (1 + k) n * (c * ph (1 + k) n) := by gcongr
  exact mul_le_mul_of_nonneg_left key (by positivity)

lemma F_bound (k n : ℕ) : |F k n| ≤ (6 * n + 4 * k + 1) * (1 / 4) ^ n := by
  rw [abs_F]
  have := F_le k n 1 (by rw [one_mul]; exact ph_le (by norm_num) (by
    have := k.cast_nonneg (α := ℝ); linarith) n) zero_le_one
  simpa using this

lemma F_bound_succ (k n : ℕ) : |F k (n + 1)| ≤ (3 * (n + 1) + 2) * (1 / 4) ^ (n + 1) := by
  rw [abs_F]
  have hk : (0 : ℝ) < 2 * (k + 1) := by positivity
  have h := F_le k (n + 1) (1 / (2 * (k + 1))) (by
    rw [one_div_mul_eq_div]; exact ph_half_le_shift k n) (by positivity)
  refine h.trans ?_
  gcongr
  rw [mul_one_div, div_le_iff₀ hk]; push_cast
  nlinarith [k.cast_nonneg (α := ℝ), n.cast_nonneg (α := ℝ)]

lemma summable_F (k : ℕ) : Summable (F k) :=
  Summable.of_norm_bounded (summable_bound (4 * k + 1)) fun n => by
    rw [Real.norm_eq_abs]; simpa [add_assoc] using F_bound k n

noncomputable def S (k : ℕ) : ℝ := ∑' n, F k n

lemma G_zero (k : ℕ) : G k 0 = 0 := by simp [G]

lemma r_pos (k : ℕ) : 0 < r k := by unfold r; positivity

lemma G_tendsto (k : ℕ) : Tendsto (G k) atTop (𝓝 0) := by
  have hb : ∀ n, |G k n| ≤ 8 * r k * (n * (1 / 4 : ℝ) ^ n) := fun n => by
    have hr := r_pos k
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [G_zero]
    have hF := F_bound k n
    have hpos : (0 : ℝ) < 6 * n + 4 * k + 1 := by positivity
    have : G k n = 8 * r k * n / (6 * n + 4 * k + 1) * F k n := by
      rw [G, F]; field_simp
    rw [this, abs_mul, abs_div, abs_of_pos hpos, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 8 * r k * n)]
    calc 8 * r k * n / (6 * n + 4 * k + 1) * |F k n| ≤ 8 * r k * n / (6 * n + 4 * k + 1) *
          ((6 * n + 4 * k + 1) * (1 / 4) ^ n) := by gcongr
      _ = _ := by field_simp
  have ht : Tendsto (fun n : ℕ => 8 * r k * ((n : ℝ) * (1 / 4 : ℝ) ^ n)) atTop (𝓝 0) := by
    simpa using (tendsto_self_mul_const_pow_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)).const_mul
      (8 * r k)
  exact squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact hb n) ht

theorem S_succ (k : ℕ) : S (k + 1) = r k * S k := by
  have hs := ((summable_F (k + 1)).hasSum.sub ((summable_F k).hasSum.mul_left (r k)))
  have h1 := hs.tendsto_sum_nat
  have h2 : (fun N => ∑ n ∈ range N, (F (k + 1) n - r k * F k n)) = G k := by
    funext N
    rw [Finset.sum_congr rfl fun n _ => cert k n, Finset.sum_range_sub, G_zero, sub_zero]
  rw [h2] at h1
  have := tendsto_nhds_unique h1 (G_tendsto k)
  rw [S, S]; linarith

noncomputable def Pr (k : ℕ) : ℝ := ∏ i ∈ range k, r i

lemma Pr_pos (k : ℕ) : 0 < Pr k := prod_pos fun i _ => r_pos i

theorem S_eq (k : ℕ) : S k = S 0 * Pr k := by
  induction k with
  | zero => simp [Pr]
  | succ k ih => rw [S_succ, ih]; simp only [Pr, prod_range_succ]; ring

lemma F_zero (k : ℕ) : F k 0 = 4 * k + 1 := by simp [F, ph_zero]

lemma tail_bound (k : ℕ) : |S k - (4 * k + 1)| ≤ C := by
  rw [S, (summable_F k).tsum_eq_zero_add, F_zero, add_sub_cancel_left]
  have hs := (summable_F k).comp_injective (add_left_injective 1)
  calc |∑' n, F k (n + 1)| ≤ ∑' n, |F k (n + 1)| := by
        simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs.norm
    _ ≤ C := Summable.tsum_le_tsum (fun n => F_bound_succ k n) hs.abs summable_C

lemma S_ratio : Tendsto (fun k : ℕ => S k / (4 * k + 1)) atTop (𝓝 1) := by
  have hd : Tendsto (fun k : ℕ => (4 * (k : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
  have h0 : Tendsto (fun k : ℕ => (S k - (4 * k + 1)) / (4 * k + 1)) atTop (𝓝 0) := by
    have hC : Tendsto (fun k : ℕ => C / (4 * (k : ℝ) + 1)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hd
    refine squeeze_zero_norm (fun k => ?_) hC
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * k + 1)]
    exact div_le_div_of_nonneg_right (tail_bound k) (by positivity)
  have := h0.const_add 1
  rw [add_zero] at this
  refine this.congr fun k => ?_
  field_simp; ring

open Real.Wallis in
lemma Pr_eq (k : ℕ) : Pr k = (2 * k + 1) * W k := by
  induction k with
  | zero => simp [Pr, W]
  | succ k ih =>
    rw [Pr, prod_range_succ, ← Pr, ih, W_succ, r]
    push_cast
    field_simp
    ring

open Real.Wallis in
lemma ratio_tendsto : Tendsto (fun k : ℕ => (4 * k + 1) / Pr k) atTop (𝓝 (4 / π)) := by
  have hq : Tendsto (fun k : ℕ => (4 * (k : ℝ) + 1) / (2 * k + 1)) atTop (𝓝 2) := by
    have : Tendsto (fun k : ℕ => 2 - 1 / ((2 * (k : ℝ)) + 1)) atTop (𝓝 (2 - 0)) := by
      refine tendsto_const_nhds.sub ?_
      exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _
        (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)))
    rw [sub_zero] at this
    refine this.congr fun k => ?_
    field_simp; ring
  have := hq.div tendsto_W_nhds_pi_div_two (by positivity)
  rw [show (2 : ℝ) / (π / 2) = 4 / π by field_simp; ring] at this
  refine this.congr fun k => ?_
  show (4 * (k : ℝ) + 1) / (2 * k + 1) / W k = _
  rw [Pr_eq]
  have := W_pos k
  field_simp

theorem S_zero : S 0 = 4 / π := by
  have h := (ratio_tendsto.mul S_ratio)
  rw [mul_one] at h
  have hc : (fun k : ℕ => (4 * (k : ℝ) + 1) / Pr k * (S k / (4 * k + 1))) = fun _ => S 0 := by
    funext k
    rw [S_eq k]
    have := Pr_pos k
    field_simp
  rw [hc] at h
  exact tendsto_nhds_unique tendsto_const_nhds h

end Four

/-- **Ramanujan's first series for `1/π`** (*Modular equations and approximations to π*, 1914):
`Σ (6n+1) ((1/2)_n)³/(n!³ 4ⁿ) = 4/π`, i.e. `1 + 7·(1/2)³/4 + 13·((1·3)/(2·4))³/4² + ⋯ = 4/π`. -/
theorem ramanujan_first_pi_series :
    HasSum (fun n : ℕ => (6 * n + 1) * ph (1 / 2) n ^ 3 / ((n ! : ℝ) ^ 3 * 4 ^ n)) (4 / π) := by
  rw [← Four.S_zero]
  convert (Four.summable_F 0).hasSum using 1
  funext n
  simp only [Four.F, Nat.cast_zero, mul_zero, add_zero, ph_one]
  have hf : (0 : ℝ) < n ! := by exact_mod_cast n.factorial_pos
  field_simp

end RamanujanPi
