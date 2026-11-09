/-
# Crude numerical enclosures of the 7-dissection components at `x₀ = e^{−π/(7√7)}`

`Σ_{n∈ℤ} x^{(7n+r)²}` splits into `Σ_{k≥0} x^{(7k+r)²} + Σ_{k≥0} x^{(7k+7−r)²}`; each half is its first term
plus a geometric tail. With `0.83 ≤ x₀ ≤ 0.8555` (from `1 − t ≤ e^{−t} ≤ 1/(1+t)`, `t = π/(7√7)`) this gives
the four inequalities `16b³c > a⁴`, `16c³d < a⁴`, `16d³b < a⁴`, `c³ > d²b` used to order the roots
(they replace Rebák's Lemmas 3.2–3.3/3.7 at this point).
-/
import RamanujanTau.Septic.RealTransfer
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false

namespace RamanujanTau.Septic

open Real

section halves

variable {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
include hx0 hx1

/-- A half-series `Σ_k x^{h k}` with `h (k+1) ≥ K + k`: summable, and `x^{h 0} ≤ Σ ≤ x^{h 0} + x^K/(1−x)`. -/
lemma half_summable (h : ℕ → ℕ) (K : ℕ) (hK : ∀ k, K + k ≤ h (k + 1)) :
    Summable fun k => x ^ h (k + 1) := by
  refine Summable.of_nonneg_of_le (fun k => pow_nonneg hx0 _) (fun k => ?_)
    ((summable_geometric_of_lt_one hx0 hx1).mul_left (x ^ K))
  rw [← pow_add]; exact pow_le_pow_of_le_one hx0 hx1.le (hK k)

lemma half_le (h : ℕ → ℕ) (K : ℕ) (hK : ∀ k, K + k ≤ h (k + 1)) :
    ∑' k, x ^ h k ≤ x ^ h 0 + x ^ K / (1 - x) := by
  rw [tsum_eq_zero_add' (f := fun k => x ^ h k) (half_summable hx0 hx1 h K hK)]
  have key : ∑' k, x ^ h (k + 1) ≤ x ^ K / (1 - x) := calc
    ∑' k, x ^ h (k + 1) ≤ ∑' k, x ^ K * x ^ k :=
        Summable.tsum_le_tsum (fun k => by rw [← pow_add]; exact pow_le_pow_of_le_one hx0 hx1.le (hK k))
          (half_summable hx0 hx1 h K hK) ((summable_geometric_of_lt_one hx0 hx1).mul_left _)
    _ = x ^ K / (1 - x) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hx0 hx1, div_eq_mul_inv]
  simp only at key ⊢
  linarith

lemma half_ge (h : ℕ → ℕ) (K : ℕ) (hK : ∀ k, K + k ≤ h (k + 1)) :
    x ^ h 0 ≤ ∑' k, x ^ h k := by
  rw [tsum_eq_zero_add' (f := fun k => x ^ h k) (half_summable hx0 hx1 h K hK)]
  have : 0 ≤ ∑' k, x ^ h (k + 1) := tsum_nonneg fun k => pow_nonneg hx0 _
  linarith

lemma half_summable' (h : ℕ → ℕ) (K : ℕ) (hK : ∀ k, K + k ≤ h (k + 1)) :
    Summable fun k => x ^ h k :=
  (summable_nat_add_iff 1).mp (half_summable hx0 hx1 h K hK)

end halves

lemma toNat_sq_nat (k r : ℕ) : ((7 * (k : ℤ) + r) ^ 2).toNat = (7 * k + r) ^ 2 := by
  have : (7 * (k : ℤ) + r) ^ 2 = (((7 * k + r) ^ 2 : ℕ) : ℤ) := by push_cast; ring
  rw [this, Int.toNat_natCast]

lemma toNat_sq_neg (k r : ℕ) (hr : r ≤ 7) :
    ((7 * (-((k : ℤ) + 1)) + r) ^ 2).toNat = (7 * k + (7 - r)) ^ 2 := by
  have : (7 * (-((k : ℤ) + 1)) + r) ^ 2 = (((7 * k + (7 - r)) ^ 2 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub hr]; ring
  rw [this, Int.toNat_natCast]

lemma sq_step (k r : ℕ) : (7 + r) ^ 2 + k ≤ (7 * (k + 1) + r) ^ 2 := by
  have e : (7 * (k + 1) + r) ^ 2 = (7 + r) ^ 2 + k * (98 + 14 * r + 49 * k) := by ring
  rw [e]
  have : k ≤ k * (98 + 14 * r + 49 * k) := Nat.le_mul_of_pos_right _ (by omega)
  omega

section TR

variable {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
include hx0 hx1

/-- `Σ_{n∈ℤ} x^{(7n+r)²}` as two half-series. -/
lemma TR_split (r : ℕ) (hr : r ≤ 7) :
    ∑' n : ℤ, x ^ ((7 * n + r) ^ 2).toNat
      = ∑' k : ℕ, x ^ ((7 * k + r) ^ 2) + ∑' k : ℕ, x ^ ((7 * k + (7 - r)) ^ 2) := by
  have h1 : Summable fun k : ℕ => x ^ ((7 * k + r) ^ 2) :=
    half_summable' hx0 hx1 (fun k => (7 * k + r) ^ 2) _ (fun k => sq_step k r)
  have h2 : Summable fun k : ℕ => x ^ ((7 * k + (7 - r)) ^ 2) :=
    half_summable' hx0 hx1 (fun k => (7 * k + (7 - r)) ^ 2) _ (fun k => sq_step k (7 - r))
  rw [tsum_of_nat_of_neg_add_one]
  · simp only [toNat_sq_nat, toNat_sq_neg _ _ hr]
  · simpa only [toNat_sq_nat] using h1
  · simpa only [toNat_sq_neg _ _ hr] using h2

lemma TR_le (r : ℕ) (hr : r ≤ 7) :
    ∑' n : ℤ, x ^ ((7 * n + r) ^ 2).toNat
      ≤ x ^ (r ^ 2) + x ^ ((7 + r) ^ 2) / (1 - x)
        + (x ^ ((7 - r) ^ 2) + x ^ ((7 + (7 - r)) ^ 2) / (1 - x)) := by
  rw [TR_split hx0 hx1 r hr]
  have a := half_le hx0 hx1 (fun k => (7 * k + r) ^ 2) _ (fun k => sq_step k r)
  have b := half_le hx0 hx1 (fun k => (7 * k + (7 - r)) ^ 2) _ (fun k => sq_step k (7 - r))
  simp only [mul_zero, zero_add] at a b
  exact add_le_add a b

lemma TR_ge (r : ℕ) (hr : r ≤ 7) :
    x ^ (r ^ 2) + x ^ ((7 - r) ^ 2) ≤ ∑' n : ℤ, x ^ ((7 * n + r) ^ 2).toNat := by
  rw [TR_split hx0 hx1 r hr]
  have a := half_ge hx0 hx1 (fun k => (7 * k + r) ^ 2) _ (fun k => sq_step k r)
  have b := half_ge hx0 hx1 (fun k => (7 * k + (7 - r)) ^ 2) _ (fun k => sq_step k (7 - r))
  simp only [mul_zero, zero_add] at a b
  exact add_le_add a b

end TR

/-! ### The point `x₀ = e^{−π/(7√7)}` -/

/-- Rebák's `q^{1/7}` at `q = e^{−π/√7}`. -/
noncomputable def x0 : ℝ := Real.exp (-π / (7 * √7))

lemma t0_bounds : 0.169 ≤ π / (7 * √7) ∧ π / (7 * √7) ≤ 0.17 := by
  have hs1 : (2.6457 : ℝ) ≤ √7 := Real.le_sqrt_of_sq_le (by norm_num)
  have hs2 : √7 ≤ (2.6458 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hp1 := pi_gt_d2
  have hp2 := pi_lt_d4
  have h7 : 0 < 7 * √7 := by positivity
  constructor
  · rw [le_div_iff₀ h7]; nlinarith
  · rw [div_le_iff₀ h7]; nlinarith

lemma x0_pos : 0 < x0 := Real.exp_pos _

lemma x0_lt_one : x0 < 1 := by
  unfold x0; rw [← Real.exp_zero]; apply Real.exp_lt_exp.mpr
  have := t0_bounds.1; rw [neg_div]; linarith

lemma x0_ge : (0.83 : ℝ) ≤ x0 := by
  unfold x0
  have := Real.add_one_le_exp (-π / (7 * √7))
  have h := t0_bounds.2; rw [neg_div] at this ⊢; linarith

lemma x0_le : x0 ≤ (0.8555 : ℝ) := by
  unfold x0
  have h1 := Real.add_one_le_exp (π / (7 * √7))
  have h := t0_bounds.1
  have hpos : 0 < Real.exp (π / (7 * √7)) := Real.exp_pos _
  rw [neg_div, Real.exp_neg, inv_le_comm₀ hpos (by norm_num)]
  linarith

/-! ### The four inequalities -/

/-- the real 7-dissection components at `x₀` -/
noncomputable def aR : ℝ := ∑' n : ℤ, x0 ^ ((7 * n + (0 : ℕ)) ^ 2).toNat
noncomputable def bR : ℝ := ∑' n : ℤ, x0 ^ ((7 * n + (1 : ℕ)) ^ 2).toNat
noncomputable def cR : ℝ := ∑' n : ℤ, x0 ^ ((7 * n + (2 : ℕ)) ^ 2).toNat
noncomputable def dR : ℝ := ∑' n : ℤ, x0 ^ ((7 * n + (3 : ℕ)) ^ 2).toNat

section ineq

local notation "xL" => (0.83 : ℝ)
local notation "xU" => (0.8555 : ℝ)

lemma hxl : xL ≤ x0 := x0_ge
lemma hxu : x0 ≤ xU := x0_le
lemma hx00 : 0 ≤ x0 := x0_pos.le

lemma pow_lo (k : ℕ) : xL ^ k ≤ x0 ^ k := pow_le_pow_left₀ (by norm_num) hxl k
lemma pow_hi (k : ℕ) : x0 ^ k ≤ xU ^ k := pow_le_pow_left₀ hx00 hxu k

lemma tail_hi (k : ℕ) : x0 ^ k / (1 - x0) ≤ xU ^ k / (1 - xU) := by
  have h1 : 0 < 1 - xU := by norm_num
  have h2 : 1 - xU ≤ 1 - x0 := by linarith [hxu]
  calc x0 ^ k / (1 - x0) ≤ xU ^ k / (1 - x0) :=
        div_le_div_of_nonneg_right (pow_hi k) (by linarith [x0_lt_one])
    _ ≤ xU ^ k / (1 - xU) := div_le_div_of_nonneg_left (by positivity) h1 h2

lemma aR_ge : 1 ≤ aR := by
  have := TR_ge hx00 x0_lt_one 0 (by norm_num)
  have h2 : 0 ≤ x0 ^ ((7 - 0) ^ 2) := pow_nonneg hx00 _
  simp only [aR]; norm_num at this h2 ⊢; linarith

lemma aR_le : aR ≤ 1.005 := by
  have := TR_le hx00 x0_lt_one 0 (by norm_num)
  have e1 := tail_hi 49; have e2 := tail_hi 196; have e3 := pow_hi 49
  simp only [aR]; norm_num at this e1 e2 e3 ⊢; linarith

lemma bR_ge : xL ≤ bR := by
  have := TR_ge hx00 x0_lt_one 1 (by norm_num)
  have h2 : 0 ≤ x0 ^ ((7 - 1) ^ 2) := pow_nonneg hx00 _
  have h3 := pow_lo 1
  simp only [bR]; norm_num at this h2 h3 ⊢; linarith

lemma bR_le : bR ≤ 0.881 := by
  have := TR_le hx00 x0_lt_one 1 (by norm_num)
  have e1 := tail_hi 64; have e2 := tail_hi 169; have e3 := pow_hi 36; have e4 := pow_hi 1
  simp only [bR]; norm_num at this e1 e2 e3 e4 ⊢; linarith

lemma cR_ge : xL ^ 4 ≤ cR := by
  have := TR_ge hx00 x0_lt_one 2 (by norm_num)
  have h2 : 0 ≤ x0 ^ ((7 - 2) ^ 2) := pow_nonneg hx00 _
  have h3 := pow_lo 4
  simp only [cR]; norm_num at this h2 h3 ⊢; linarith

lemma cR_le : cR ≤ 0.556 := by
  have := TR_le hx00 x0_lt_one 2 (by norm_num)
  have e1 := tail_hi 81; have e2 := tail_hi 144; have e3 := pow_hi 25; have e4 := pow_hi 4
  simp only [cR]; norm_num at this e1 e2 e3 e4 ⊢; linarith

lemma dR_ge : 0 < dR := by
  have := TR_ge hx00 x0_lt_one 3 (by norm_num)
  have h2 : 0 < x0 ^ (3 ^ 2) + x0 ^ ((7 - 3) ^ 2) := by have := x0_pos; positivity
  simp only [dR]; linarith

lemma dR_le : dR ≤ 0.328 := by
  have := TR_le hx00 x0_lt_one 3 (by norm_num)
  have e1 := tail_hi 100; have e2 := tail_hi 121; have e3 := pow_hi 9; have e4 := pow_hi 16
  simp only [dR]; norm_num at this e1 e2 e3 e4 ⊢; linarith

lemma bR_pos : 0 < bR := lt_of_lt_of_le (by norm_num) bR_ge
lemma cR_pos : 0 < cR := lt_of_lt_of_le (by norm_num) cR_ge
lemma aR_pos : 0 < aR := lt_of_lt_of_le (by norm_num) aR_ge

/-- `u³v > 1`. -/
theorem ineq_s1 : aR ^ 4 < 16 * bR ^ 3 * cR := by
  have ha := aR_le; have hb := bR_ge; have hc := cR_ge
  have ha0 := aR_pos
  have h1 : aR ^ 4 ≤ 1.005 ^ 4 := pow_le_pow_left₀ ha0.le ha 4
  have h2 : (0.83 : ℝ) ^ 3 ≤ bR ^ 3 := pow_le_pow_left₀ (by norm_num) hb 3
  have h3 : 16 * (0.83 : ℝ) ^ 3 * 0.83 ^ 4 ≤ 16 * bR ^ 3 * cR := by
    have : (0 : ℝ) ≤ 0.83 ^ 3 := by norm_num
    nlinarith
  norm_num at h1 h3 ⊢; linarith

/-- `v³w < 1`. -/
theorem ineq_s2 : 16 * cR ^ 3 * dR < aR ^ 4 := by
  have h1 : (1 : ℝ) ≤ aR ^ 4 := one_le_pow₀ aR_ge
  have h2 : cR ^ 3 ≤ 0.556 ^ 3 := pow_le_pow_left₀ cR_pos.le cR_le 3
  have h3 : 16 * cR ^ 3 * dR ≤ 16 * 0.556 ^ 3 * 0.328 := by
    have := dR_ge; have := dR_le
    have : 0 ≤ cR ^ 3 := by have := cR_pos; positivity
    nlinarith
  norm_num at h3; linarith

/-- `w³u < 1`. -/
theorem ineq_s3 : 16 * dR ^ 3 * bR < aR ^ 4 := by
  have h1 : (1 : ℝ) ≤ aR ^ 4 := one_le_pow₀ aR_ge
  have h2 : dR ^ 3 ≤ 0.328 ^ 3 := pow_le_pow_left₀ dR_ge.le dR_le 3
  have h3 : 16 * dR ^ 3 * bR ≤ 16 * 0.328 ^ 3 * 0.881 := by
    have := bR_pos; have := bR_le
    have : 0 ≤ dR ^ 3 := by have := dR_ge; positivity
    nlinarith
  norm_num at h3; linarith

/-- `v³w > w³u`, i.e. `c³ > d²b`. -/
theorem ineq_s23 : dR ^ 2 * bR < cR ^ 3 := by
  have h2 : dR ^ 2 ≤ 0.328 ^ 2 := pow_le_pow_left₀ dR_ge.le dR_le 2
  have h3 : dR ^ 2 * bR ≤ 0.328 ^ 2 * 0.881 := by
    have := bR_pos; have := bR_le
    have : 0 ≤ dR ^ 2 := sq_nonneg _
    nlinarith
  have h4 : ((0.83 : ℝ) ^ 4) ^ 3 ≤ cR ^ 3 := pow_le_pow_left₀ (by norm_num) cR_ge 3
  norm_num at h3 h4 ⊢; linarith

end ineq

end RamanujanTau.Septic
