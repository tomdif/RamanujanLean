/-
# Euler's series `S(x) = Σ xⁿ r^{n²}/(r²;r²)_n = (−xr;r²)_∞` for real `0 ≤ r < 1`, `0 ≤ x ≤ 1`

Proof by the functional equation `S(x) = (1 + xr) S(xr²)`, iterated, with `S(y) → 1` as `y → 0`.
Consequences used for the bound on `φ`:
* `S(1/2) ≤ S(1) e^{−r/(4(1−r²))}`;
* `S(1) = (−r;r²)_∞`, i.e. `Oz r`.
-/
import RamanujanTau.Dragonette.Odd

set_option autoImplicit false

namespace Dragonette
open Finset Filter
open scoped Topology

/-- `c_n = r^{n²}/(r²;r²)_n`. -/
noncomputable def cn (r : ℝ) (n : ℕ) : ℝ := r ^ (n ^ 2) / ∏ i ∈ range n, (1 - r ^ (2 * (i + 1)))

/-- `S(x) = Σ c_n xⁿ`. -/
noncomputable def Sx (r x : ℝ) : ℝ := ∑' n, cn r n * x ^ n

/-- the partial products `∏_{k<K}(1 + x r r^{2k})`. -/
noncomputable def Pk (r x : ℝ) (K : ℕ) : ℝ := ∏ k ∈ range K, (1 + x * r * (r ^ 2) ^ k)

section
variable {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1)
include h0 h1

lemma rpow_lt {m : ℕ} (hm : m ≠ 0) : r ^ m < 1 := pow_lt_one₀ h0 h1 hm

lemma qpoch_ge (n : ℕ) : (1 - r ^ 2) ^ n ≤ ∏ i ∈ range n, (1 - r ^ (2 * (i + 1))) := by
  calc (1 - r ^ 2) ^ n = ∏ _i ∈ range n, (1 - r ^ 2) := by simp
    _ ≤ _ := by
      refine Finset.prod_le_prod (fun i _ => by nlinarith [rpow_lt h0 h1 (m := 2) (by norm_num)]) fun i _ => ?_
      have : r ^ (2 * (i + 1)) ≤ r ^ 2 := pow_le_pow_of_le_one h0 h1.le (by omega)
      linarith

lemma qpoch_pos (n : ℕ) : 0 < ∏ i ∈ range n, (1 - r ^ (2 * (i + 1))) :=
  Finset.prod_pos fun i _ => by linarith [rpow_lt h0 h1 (m := 2 * (i + 1)) (by omega)]

lemma cn_nonneg (n : ℕ) : 0 ≤ cn r n := div_nonneg (pow_nonneg h0 _) (qpoch_pos h0 h1 n).le

lemma cn_zero : cn r 0 = 1 := by simp [cn]

lemma cn_le (n : ℕ) : cn r n ≤ r ^ (n ^ 2) * (1 / (1 - r ^ 2)) ^ n := by
  have hq : 0 < 1 - r ^ 2 := by nlinarith [rpow_lt h0 h1 (m := 2) (by norm_num)]
  rw [cn, div_le_iff₀ (qpoch_pos h0 h1 n), one_div, inv_pow, mul_assoc]
  have := qpoch_ge h0 h1 n
  have hp : 0 < (1 - r ^ 2) ^ n := pow_pos hq n
  calc r ^ (n ^ 2) = r ^ (n ^ 2) * (((1 - r ^ 2) ^ n)⁻¹ * (1 - r ^ 2) ^ n) := by
        rw [inv_mul_cancel₀ hp.ne', mul_one]
    _ ≤ _ := by gcongr

lemma summable_cn {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : Summable fun n => cn r n * x ^ n := by
  have hq : 0 < 1 - r ^ 2 := by nlinarith [rpow_lt h0 h1 (m := 2) (by norm_num)]
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (cn_nonneg h0 h1 n) (pow_nonneg hx0 n)) (fun n => ?_)
    (Taylor.summable_sq_mul_pow h0 h1 (1 / (1 - r ^ 2)) (by positivity))
  calc cn r n * x ^ n ≤ cn r n * 1 := by
        gcongr
        · exact cn_nonneg h0 h1 n
        · exact pow_le_one₀ hx0 hx1
    _ ≤ _ := by rw [mul_one]; exact cn_le h0 h1 n

lemma cn_succ (n : ℕ) : cn r (n + 1) * (1 - r ^ (2 * (n + 1))) = cn r n * r ^ (2 * n + 1) := by
  have hp := qpoch_pos h0 h1 n
  have hl : 0 < 1 - r ^ (2 * (n + 1)) := by linarith [rpow_lt h0 h1 (m := 2 * (n + 1)) (by omega)]
  unfold cn
  rw [prod_range_succ]
  field_simp
  rw [← pow_add]; congr 1; ring

/-- **the functional equation** `S(x) = (1 + xr) S(xr²)`. -/
lemma Sx_func {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : Sx r x = (1 + x * r) * Sx r (x * r ^ 2) := by
  have hr2 : r ^ 2 ≤ 1 := pow_le_one₀ h0 h1.le
  have hy0 : 0 ≤ x * r ^ 2 := by positivity
  have hy1 : x * r ^ 2 ≤ 1 := by nlinarith
  have hA := summable_cn h0 h1 hx0 hx1
  have hB := summable_cn h0 h1 hy0 hy1
  have hdiff : Sx r x - Sx r (x * r ^ 2) = x * r * Sx r (x * r ^ 2) := by
    unfold Sx
    rw [← hA.tsum_sub hB]
    have hC := hA.sub hB
    rw [hC.tsum_eq_zero_add, ← hB.tsum_mul_left]
    simp only [pow_zero, mul_one, sub_self, zero_add]
    congr 1; funext n
    have := cn_succ h0 h1 n
    have e : cn r (n + 1) * x ^ (n + 1) - cn r (n + 1) * (x * r ^ 2) ^ (n + 1) =
        x ^ (n + 1) * (cn r (n + 1) * (1 - r ^ (2 * (n + 1)))) := by
      rw [mul_pow, ← pow_mul]; ring
    rw [e, this, mul_pow, ← pow_mul]
    ring_nf
  linarith

lemma Sx_iter : ∀ K : ℕ, ∀ x : ℝ, 0 ≤ x → x ≤ 1 → Sx r x = Pk r x K * Sx r (x * (r ^ 2) ^ K) := by
  have hr2 : r ^ 2 ≤ 1 := pow_le_one₀ h0 h1.le
  intro K
  induction K with
  | zero => intro x _ _; simp [Pk]
  | succ K ih =>
    intro x hx0 hx1
    have hy0 : 0 ≤ x * r ^ 2 := by positivity
    have hy1 : x * r ^ 2 ≤ 1 := by nlinarith
    have hP : Pk r x (K + 1) = Pk r (x * r ^ 2) K * (1 + x * r) := by
      rw [Pk, Pk, prod_range_succ']
      congr 1
      · exact Finset.prod_congr rfl fun k _ => by ring
      · ring
    rw [Sx_func h0 h1 hx0 hx1, ih (x * r ^ 2) hy0 hy1, hP,
      show x * (r ^ 2) ^ (K + 1) = x * r ^ 2 * (r ^ 2) ^ K by ring]
    ring

lemma Sx_ge_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 1 ≤ Sx r x := by
  have hA := summable_cn h0 h1 hx0 hx1
  unfold Sx
  rw [hA.tsum_eq_zero_add, cn_zero h0 h1]
  simp only [pow_zero, mul_one]
  have : 0 ≤ ∑' n : ℕ, cn r (n + 1) * x ^ (n + 1) :=
    tsum_nonneg fun n => mul_nonneg (cn_nonneg h0 h1 (n + 1)) (pow_nonneg hx0 (n + 1))
  linarith

lemma Sx_sub_one {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : Sx r y - 1 ≤ y * Sx r 1 := by
  have hA := summable_cn h0 h1 hy0 hy1
  have h1' := summable_cn h0 h1 zero_le_one le_rfl
  unfold Sx
  rw [hA.tsum_eq_zero_add, h1'.tsum_eq_zero_add, cn_zero h0 h1]
  simp only [pow_zero, mul_one, one_pow, add_sub_cancel_left]
  have hs1 : Summable fun n : ℕ => cn r (n + 1) * y ^ (n + 1) := (summable_nat_add_iff 1).mpr hA
  have hs2 : Summable fun n : ℕ => cn r (n + 1) := by
    have := (summable_nat_add_iff 1).mpr h1'; simpa using this
  have hle : ∑' n : ℕ, cn r (n + 1) * y ^ (n + 1) ≤ ∑' n : ℕ, y * cn r (n + 1) := by
    refine hs1.tsum_le_tsum (fun n => ?_) (hs2.mul_left y)
    rw [pow_succ, mul_comm (y ^ n) y, ← mul_assoc, mul_comm (cn r (n + 1)) y, mul_assoc]
    have := cn_nonneg h0 h1 (n + 1)
    have : y ^ n ≤ 1 := pow_le_one₀ hy0 hy1
    nlinarith [mul_nonneg hy0 (cn_nonneg h0 h1 (n + 1))]
  rw [hs2.tsum_mul_left] at hle
  have : 0 ≤ ∑' n : ℕ, cn r (n + 1) := tsum_nonneg fun n => cn_nonneg h0 h1 (n + 1)
  nlinarith

/-- the partial products converge to `S(x)`. -/
lemma Pk_tendsto {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : Tendsto (Pk r x) atTop (𝓝 (Sx r x)) := by
  have hr2 : r ^ 2 < 1 := rpow_lt h0 h1 (by norm_num)
  have hg : Tendsto (fun K : ℕ => x * (r ^ 2) ^ K) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hr2).const_mul x
  have hy0 : ∀ K : ℕ, 0 ≤ x * (r ^ 2) ^ K := fun K => by positivity
  have hy1 : ∀ K : ℕ, x * (r ^ 2) ^ K ≤ 1 := fun K =>
    mul_le_one₀ hx1 (pow_nonneg (by positivity) _) (pow_le_one₀ (by positivity) hr2.le)
  -- `S(x r^{2K}) → 1`
  have hS : Tendsto (fun K : ℕ => Sx r (x * (r ^ 2) ^ K)) atTop (𝓝 1) := by
    have hu : Tendsto (fun K : ℕ => 1 + x * (r ^ 2) ^ K * Sx r 1) atTop (𝓝 1) := by
      simpa using (hg.mul_const (Sx r 1)).const_add 1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu (fun K => ?_) (fun K => ?_)
    · exact Sx_ge_one h0 h1 (hy0 K) (hy1 K)
    · have := Sx_sub_one h0 h1 (hy0 K) (hy1 K); simp only; linarith
  have hS' := hS.inv₀ one_ne_zero
  have := hS'.const_mul (Sx r x)
  rw [inv_one, mul_one] at this
  refine this.congr fun K => ?_
  have hpos : 0 < Sx r (x * (r ^ 2) ^ K) := lt_of_lt_of_le one_pos (Sx_ge_one h0 h1 (hy0 K) (hy1 K))
  rw [Sx_iter h0 h1 K x hx0 hx1]
  field_simp

/-- **`S(1/2) ≤ S(1)·e^{−r/(4(1−r²))}`**. -/
lemma Sx_half : Sx r (1 / 2) ≤ Sx r 1 * Real.exp (-(r / (1 - r ^ 2)) / 4) := by
  have hr2 : r ^ 2 < 1 := rpow_lt h0 h1 (by norm_num)
  have hgeo : HasSum (fun k : ℕ => r * (r ^ 2) ^ k) (r / (1 - r ^ 2)) := by
    have := (hasSum_geometric_of_lt_one (by positivity) hr2).mul_left r
    simpa [div_eq_mul_inv] using this
  have hT := (Pk_tendsto h0 h1 zero_le_one le_rfl).mul
    ((Real.continuous_exp.tendsto _).comp ((hgeo.tendsto_sum_nat.neg).div_const 4))
  refine le_of_tendsto_of_tendsto' (Pk_tendsto h0 h1 (by norm_num) (by norm_num)) hT fun K => ?_
  simp only [Function.comp, Pk]
  rw [← Finset.sum_neg_distrib, Finset.sum_div, Real.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun k _ => by positivity) fun k _ => ?_
  obtain ⟨y, hy⟩ : ∃ y, y = r * (r ^ 2) ^ k := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hy1 : y ≤ 1 := by rw [hy]; exact mul_le_one₀ h1.le (by positivity) (pow_le_one₀ (by positivity) hr2.le)
  have he : 1 - y / 4 ≤ Real.exp (-y / 4) := by linarith [Real.add_one_le_exp (-y / 4)]
  rw [show 1 + 1 / 2 * r * (r ^ 2) ^ k = 1 + y / 2 by rw [hy]; ring,
    show 1 + 1 * r * (r ^ 2) ^ k = 1 + y by rw [hy]; ring, ← hy]
  calc 1 + y / 2 ≤ (1 + y) * (1 - y / 4) := by nlinarith
    _ ≤ (1 + y) * Real.exp (-y / 4) := by gcongr
    _ = _ := by ring_nf
end

/-- **`S(1) = (−r;r²)_∞`**. -/
lemma Oz_ofReal {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) : Oz (r : ℂ) = ((Sx r 1 : ℝ) : ℂ) := by
  have hs : ‖(r : ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_of_nonneg h0]; exact h1
  have hm := (mult_one_add_pow hs (fun k => 2 * k + 1) (fun k => by dsimp only; omega)).hasProd.tendsto_prod_nat
  have hP := (Complex.continuous_ofReal.tendsto _).comp (Pk_tendsto h0 h1 zero_le_one le_rfl)
  refine tendsto_nhds_unique hm (hP.congr fun K => ?_)
  simp only [Function.comp, Pk]
  push_cast
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [one_mul, ← pow_mul, ← pow_succ']

lemma Sx_one_eq {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) : Sx r 1 = ‖Oz (r : ℂ)‖ := by
  rw [Oz_ofReal h0 h1, Complex.norm_real, Real.norm_of_nonneg (by linarith [Sx_ge_one h0 h1 zero_le_one le_rfl])]

end Dragonette
