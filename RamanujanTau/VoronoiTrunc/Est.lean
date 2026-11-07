/-
# Estimates feeding the `L²` assembly

* `kB_zero_sub_main`: `|k₀(n,y) − y^{23/4} n^{−25/4} cos(4π√n√y − π/4)/(π√2)| ≤ C y^{11/2} n^{−13/2}`
  (`n, y ≥ 1`), from `Ik_asymp_twelve` and `kB_eq_Ik`;
* `norm_kB_twelve_le`: `‖k₁₂(n,y)‖ ≤ C y^{12} n^{−12} (ny)^{−1/4}`, from `Ik_bound`;
* Rankin-trick sums for `Σ|τ(n)| n^{−α}` (head and tail);
* `abs_mK_sub_le`: a Lipschitz bound for the main term;
* `integral_short_sq_le`: `∫_X^{2X} (Σ_{x<n≤x+H} |τ(n)|)² ≤ (H+1) H Σ_{n≤3X} τ(n)²`.
-/
import RamanujanTau.VoronoiTrunc.Avg
import RamanujanTau.VoronoiTrunc.MeanValue

set_option autoImplicit false

namespace RamanujanTau.VoronoiTrunc

open Complex Real MeasureTheory Set Filter Topology

/-- The main term `m(n,y) = y^{23/4} n^{−25/4} cos(4π√n√y − π/4)/(π√2)`. -/
noncomputable def mK (n : ℕ) (y : ℝ) : ℝ :=
  y ^ (23 / 4 : ℝ) * (n : ℝ) ^ (-(25 / 4) : ℝ) / (π * √2) * Real.cos (th n y)

lemma continuous_mK (n : ℕ) : Continuous (mK n) := by
  unfold mK th
  have : Continuous fun y : ℝ => y ^ (23 / 4 : ℝ) := Real.continuous_rpow_const (by norm_num)
  fun_prop

/-- The `rpow` identity `(y/n)^6 / √(π · 2π√(ny)) = y^{23/4} n^{−25/4}/(π√2)`. -/
lemma rpow_identity {n y : ℝ} (hn : 0 < n) (hy : 0 < y) :
    (y / n) ^ 6 / √(π * (2 * π * √(n * y))) = y ^ (23 / 4 : ℝ) * n ^ (-(25 / 4) : ℝ) / (π * √2) := by
  have hp := Real.pi_pos
  have e1 : √(π * (2 * π * √(n * y))) = π * √2 * (n ^ (1 / 4 : ℝ) * y ^ (1 / 4 : ℝ)) := by
    rw [show π * (2 * π * √(n * y)) = (π * √2) ^ 2 * √(n * y) by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    congr 1
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity),
      Real.mul_rpow hn.le hy.le]
    norm_num
  rw [e1]
  have h1 : y ^ (23 / 4 : ℝ) = y ^ (6 : ℝ) * (y ^ (1 / 4 : ℝ))⁻¹ := by
    rw [← Real.rpow_neg hy.le, ← Real.rpow_add hy]; norm_num
  have h2 : n ^ (-(25 / 4) : ℝ) = (n ^ (6 : ℝ))⁻¹ * (n ^ (1 / 4 : ℝ))⁻¹ := by
    rw [← Real.rpow_neg hn.le, ← Real.rpow_neg hn.le, ← Real.rpow_add hn]; norm_num
  rw [h1, h2, div_pow]
  rw [show ((y : ℝ) ^ 6) = y ^ (6 : ℝ) by norm_cast, show ((n : ℝ) ^ 6) = n ^ (6 : ℝ) by norm_cast]
  have : 0 < n ^ (1 / 4 : ℝ) := by positivity
  have : 0 < y ^ (1 / 4 : ℝ) := by positivity
  have : 0 < n ^ (6 : ℝ) := by positivity
  have : (0 : ℝ) < √2 := by positivity
  field_simp

lemma sqrt_mul_nat (n : ℕ) (y : ℝ) : √((n : ℝ) * y) = √(n : ℝ) * √y :=
  Real.sqrt_mul (Nat.cast_nonneg n) y

/-- The constant in `kB_zero_sub_main`. -/
noncomputable def CK : ℝ := Ck 12 / (2 * π ^ 2)

/-- **Kernel → main term**: `‖k₀(n,y) − m(n,y)‖ ≤ C_K y^{11/2} n^{−13/2}`. -/
theorem kB_zero_sub_main {n : ℕ} (hn : 1 ≤ n) {y : ℝ} (hy : 1 ≤ y) :
    ‖kB 0 n y - (mK n y : ℂ)‖ ≤ CK * y ^ (11 / 2 : ℝ) * (n : ℝ) ^ (-(13 / 2) : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hy0 : 0 < y := by linarith
  rw [kB_eq_Ik 0 hn hy0, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  set L := 2 * π * √((n : ℝ) * y) with hL
  have hL0 : 0 < L := by positivity
  have hA := Ik_asymp_twelve hL0
  have h12 : (√(y / n)) ^ (12 + 0) = (y / n) ^ 6 := by
    rw [show 12 + 0 = 2 * 6 by rfl, pow_mul, Real.sq_sqrt (by positivity)]
  rw [h12]
  have hth : th n y = 2 * L - π / 4 := by unfold th; rw [hL, sqrt_mul_nat]; ring
  have hmain : mK n y = (y / n) ^ 6 * (Real.cos (2 * L - π / 4) / √(π * L)) := by
    unfold mK
    rw [hth, ← rpow_identity hn0 hy0, ← hL]; ring
  rw [hmain, ← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
  calc (y / n) ^ 6 * |Ik 12 L - Real.cos (2 * L - π / 4) / √(π * L)|
      ≤ (y / n) ^ 6 * (Ck 12 / (π * L)) := by gcongr
    _ = CK * y ^ (11 / 2 : ℝ) * (n : ℝ) ^ (-(13 / 2) : ℝ) := by
        unfold CK
        rw [hL, Real.sqrt_mul hn0.le]
        have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
        have hsy : 0 < √y := Real.sqrt_pos.2 hy0
        have e1 : y ^ (11 / 2 : ℝ) = y ^ 6 / √y := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_sub hy0]; norm_num
        have e2 : (n : ℝ) ^ (-(13 / 2) : ℝ) = 1 / ((n : ℝ) ^ 6 * √(n : ℝ)) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hn0, Real.rpow_neg hn0.le]
          norm_num
        rw [e1, e2]
        field_simp

/-- The constant in `norm_kB_twelve_le`. -/
noncomputable def CT : ℝ := (2 * √π + Ck 24) / √(2 * π)

/-- **Top kernel bound** (`r = 12`): `‖k₁₂(n,y)‖ ≤ C_T y^{12} n^{−12} (ny)^{−1/4}`. -/
theorem norm_kB_twelve_le {n : ℕ} (hn : 1 ≤ n) {y : ℝ} (hy : 1 ≤ y) :
    ‖kB 12 n y‖ ≤ CT * y ^ 12 * ((n : ℝ) ^ 12)⁻¹ * ((n : ℝ) * y) ^ (-(1 / 4) : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hy0 : 0 < y := by linarith
  rw [kB_eq_Ik 12 hn hy0, Complex.norm_real, Real.norm_eq_abs]
  set L := 2 * π * √((n : ℝ) * y) with hL
  have hny : 1 ≤ (n : ℝ) * y := by nlinarith [(by exact_mod_cast hn : (1 : ℝ) ≤ n)]
  have hL1 : 1 ≤ L := by
    have : 1 ≤ √((n : ℝ) * y) := by rw [Real.le_sqrt (by norm_num) (by positivity)]; simpa using hny
    nlinarith [Real.two_le_pi]
  have hB := Ik_bound (ν := 12 + 12) (by norm_num) hL1
  have h24 : (√(y / n)) ^ (12 + 12) = (y / n) ^ 12 := by
    rw [show 12 + 12 = 2 * 12 by rfl, pow_mul, Real.sq_sqrt (by positivity)]
  rw [abs_mul, h24, abs_of_nonneg (by positivity)]
  have hsL : √L = √(2 * π) * ((n : ℝ) * y) ^ (1 / 4 : ℝ) := by
    rw [hL, Real.sqrt_mul (by positivity)]
    congr 1
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
    norm_num
  calc (y / n) ^ 12 * |Ik (12 + 12) L| ≤ (y / n) ^ 12 * ((2 * √π + Ck (12 + 12)) / √L) := by gcongr
    _ = CT * y ^ 12 * ((n : ℝ) ^ 12)⁻¹ * ((n : ℝ) * y) ^ (-(1 / 4) : ℝ) := by
        unfold CT
        rw [hsL, Real.rpow_neg (by positivity)]
        have : 0 < ((n : ℝ) * y) ^ (1 / 4 : ℝ) := by positivity
        have : 0 < √(2 * π) := by positivity
        field_simp


/-! ### Rankin-trick sums -/

/-- `St β = Σ |τ(n)| n^{−β}`. -/
noncomputable def St (β : ℝ) : ℝ := ∑' n : ℕ, |((tau n : ℤ) : ℝ)| / (n : ℝ) ^ β

lemma summable_St {β : ℝ} (hβ : 13 / 2 < β) :
    Summable fun n : ℕ => |((tau n : ℤ) : ℝ)| / (n : ℝ) ^ β :=
  RamanujanTau.HeckeConvex.summable_abs_tau_div_rpow hβ

lemma St_nonneg (β : ℝ) : 0 ≤ St β := tsum_nonneg fun n => by positivity

/-- Head: `Σ_{n≤M} |τ(n)| n^{−γ} ≤ M^{β−γ} St(β)` for `γ ≤ β`, `β > 13/2`. -/
lemma head_sum_le {β γ : ℝ} (hβ : 13 / 2 < β) (hγ : γ ≤ β) (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, |((tau n : ℤ) : ℝ)| * (n : ℝ) ^ (-γ) ≤ (M : ℝ) ^ (β - γ) * St β := by
  have hs := summable_St hβ
  have h1 : ∀ n ∈ Finset.Icc 1 M, |((tau n : ℤ) : ℝ)| * (n : ℝ) ^ (-γ) ≤
      (M : ℝ) ^ (β - γ) * (|((tau n : ℤ) : ℝ)| / (n : ℝ) ^ β) := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
    have hnM : (n : ℝ) ≤ M := by exact_mod_cast h2
    have e : (n : ℝ) ^ (-γ) = (n : ℝ) ^ (β - γ) * ((n : ℝ) ^ β)⁻¹ := by
      rw [← Real.rpow_neg hn0.le, ← Real.rpow_add hn0]; congr 1; ring
    rw [e, div_eq_mul_inv]
    have : (n : ℝ) ^ (β - γ) ≤ (M : ℝ) ^ (β - γ) := Real.rpow_le_rpow hn0.le hnM (by linarith)
    have h0 : 0 ≤ |((tau n : ℤ) : ℝ)| * ((n : ℝ) ^ β)⁻¹ := by positivity
    nlinarith
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact hs.sum_le_tsum _ fun n _ => by positivity

lemma rpow_trick {a m M1 α β : ℝ} (ha : 0 ≤ a) (hM1 : 0 < M1) (hm : M1 ≤ m) (hαβ : β ≤ α) :
    a * m ^ (-α) ≤ M1 ^ (β - α) * (a / m ^ β) := by
  have hm0 : 0 < m := lt_of_lt_of_le hM1 hm
  have e : m ^ (-α) = m ^ (β - α) * (m ^ β)⁻¹ := by
    rw [← Real.rpow_neg hm0.le, ← Real.rpow_add hm0]; congr 1; ring
  rw [e, div_eq_mul_inv]
  have : m ^ (β - α) ≤ M1 ^ (β - α) := Real.rpow_le_rpow_of_nonpos hM1 hm (by linarith)
  have h0 : 0 ≤ a * (m ^ β)⁻¹ := by positivity
  nlinarith

/-- Tail: `Σ_{n>M} |τ(n)| n^{−α} ≤ (M+1)^{β−α} St(β)` for `13/2 < β ≤ α`. -/
lemma tail_sum_le {α β : ℝ} (hβ : 13 / 2 < β) (hαβ : β ≤ α) (M : ℕ) :
    Summable (fun k : ℕ => |((tau (k + (M + 1)) : ℤ) : ℝ)| * ((k + (M + 1) : ℕ) : ℝ) ^ (-α)) ∧
    ∑' k : ℕ, |((tau (k + (M + 1)) : ℤ) : ℝ)| * ((k + (M + 1) : ℕ) : ℝ) ^ (-α) ≤
      ((M : ℝ) + 1) ^ (β - α) * St β := by
  have hs := summable_St hβ
  have hs' := (summable_nat_add_iff (M + 1)).2 hs
  have hb : ∀ k : ℕ, |((tau (k + (M + 1)) : ℤ) : ℝ)| * ((k + (M + 1) : ℕ) : ℝ) ^ (-α) ≤
      ((M : ℝ) + 1) ^ (β - α) * (|((tau (k + (M + 1)) : ℤ) : ℝ)| / ((k + (M + 1) : ℕ) : ℝ) ^ β) := by
    intro k
    have hnM : (M : ℝ) + 1 ≤ ((k + (M + 1) : ℕ) : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) k]
    exact rpow_trick (abs_nonneg _) (by positivity) hnM hαβ
  have hsum : Summable fun k : ℕ => ((M : ℝ) + 1) ^ (β - α) *
      (|((tau (k + (M + 1)) : ℤ) : ℝ)| / ((k + (M + 1) : ℕ) : ℝ) ^ β) :=
    hs'.mul_left (((M : ℝ) + 1) ^ (β - α))
  refine ⟨Summable.of_nonneg_of_le (fun k => by positivity) hb hsum, ?_⟩
  refine (Summable.tsum_le_tsum hb (Summable.of_nonneg_of_le (fun k => by positivity) hb hsum) hsum).trans ?_
  rw [tsum_mul_left]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have := (hs.sum_add_tsum_nat_add (M + 1)).symm
  have h0 : 0 ≤ ∑ n ∈ Finset.range (M + 1), |((tau n : ℤ) : ℝ)| / (n : ℝ) ^ β :=
    Finset.sum_nonneg fun n _ => by positivity
  unfold St
  linarith

/-! ### A Lipschitz bound for the main term -/

lemma hasDerivAt_main (n : ℕ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y => y ^ (23 / 4 : ℝ) * Real.cos (th n y))
      ((23 / 4) * y ^ (23 / 4 - 1 : ℝ) * Real.cos (th n y) -
        y ^ (23 / 4 : ℝ) * (Real.sin (th n y) * (4 * π * √(n : ℝ) * (1 / (2 * √y))))) y := by
  have h1 := Real.hasDerivAt_rpow_const (x := y) (p := 23 / 4) (Or.inl hy.ne')
  have hs : HasDerivAt (fun y => √y) (1 / (2 * √y)) y := by
    have := Real.hasDerivAt_sqrt hy.ne'; simpa using this
  have h2 : HasDerivAt (th n) (4 * π * √(n : ℝ) * (1 / (2 * √y))) y := by
    unfold th
    exact (hs.const_mul (4 * π * √(n : ℝ))).sub_const (π / 4)
  have h3 := h1.mul h2.cos
  convert h3 using 1; ring

lemma abs_main_sub_le (n : ℕ) {x x' Y : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ x') (h3 : x' ≤ Y) :
    |x' ^ (23 / 4 : ℝ) * Real.cos (th n x') - x ^ (23 / 4 : ℝ) * Real.cos (th n x)| ≤
      (6 + 2 * π * √(n : ℝ)) * Y ^ (21 / 4 : ℝ) * (x' - x) := by
  have hY : 1 ≤ Y := by linarith
  have hd : ∀ y ∈ Icc x x', HasDerivWithinAt (fun y => y ^ (23 / 4 : ℝ) * Real.cos (th n y))
      ((23 / 4) * y ^ (23 / 4 - 1 : ℝ) * Real.cos (th n y) -
        y ^ (23 / 4 : ℝ) * (Real.sin (th n y) * (4 * π * √(n : ℝ) * (1 / (2 * √y))))) (Icc x x') y :=
    fun y hy => (hasDerivAt_main n (by linarith [hy.1])).hasDerivWithinAt
  have hb : ∀ y ∈ Ico x x', ‖(23 / 4) * y ^ (23 / 4 - 1 : ℝ) * Real.cos (th n y) -
      y ^ (23 / 4 : ℝ) * (Real.sin (th n y) * (4 * π * √(n : ℝ) * (1 / (2 * √y))))‖ ≤
      (6 + 2 * π * √(n : ℝ)) * Y ^ (21 / 4 : ℝ) := by
    intro y hy
    have hy1 : 1 ≤ y := le_trans h1 hy.1
    have hyY : y ≤ Y := by linarith [hy.2]
    have hy0 : 0 < y := by linarith
    have hsy : 0 < √y := Real.sqrt_pos.2 hy0
    rw [Real.norm_eq_abs]
    have hA : |(23 / 4) * y ^ (23 / 4 - 1 : ℝ) * Real.cos (th n y)| ≤ 6 * Y ^ (21 / 4 : ℝ) := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 23 / 4), abs_of_pos (by positivity)]
      have hc := Real.abs_cos_le_one (th n y)
      have : y ^ (23 / 4 - 1 : ℝ) ≤ Y ^ (21 / 4 : ℝ) := by
        calc y ^ (23 / 4 - 1 : ℝ) ≤ y ^ (21 / 4 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num)
          _ ≤ Y ^ (21 / 4 : ℝ) := Real.rpow_le_rpow hy0.le hyY (by norm_num)
      have hp : 0 ≤ y ^ (23 / 4 - 1 : ℝ) := by positivity
      nlinarith [abs_nonneg (Real.cos (th n y))]
    have hB : |y ^ (23 / 4 : ℝ) * (Real.sin (th n y) * (4 * π * √(n : ℝ) * (1 / (2 * √y))))| ≤
        2 * π * √(n : ℝ) * Y ^ (21 / 4 : ℝ) := by
      have e : y ^ (23 / 4 : ℝ) * (1 / (2 * √y)) = y ^ (21 / 4 : ℝ) / 2 := by
        rw [Real.sqrt_eq_rpow]
        have : y ^ (23 / 4 : ℝ) = y ^ (21 / 4 : ℝ) * y ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_add hy0]; norm_num
        rw [this]; field_simp
      have e2 : y ^ (23 / 4 : ℝ) * (Real.sin (th n y) * (4 * π * √(n : ℝ) * (1 / (2 * √y)))) =
          Real.sin (th n y) * (2 * π * √(n : ℝ)) * y ^ (21 / 4 : ℝ) := by
        rw [show y ^ (23 / 4 : ℝ) * (Real.sin (th n y) * (4 * π * √(n : ℝ) * (1 / (2 * √y)))) =
          Real.sin (th n y) * (4 * π * √(n : ℝ)) * (y ^ (23 / 4 : ℝ) * (1 / (2 * √y))) by ring, e]
        ring
      rw [e2, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * π * √(n : ℝ)),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ y ^ (21 / 4 : ℝ))]
      have hs := Real.abs_sin_le_one (th n y)
      have : y ^ (21 / 4 : ℝ) ≤ Y ^ (21 / 4 : ℝ) := Real.rpow_le_rpow hy0.le hyY (by norm_num)
      have hp : 0 ≤ 2 * π * √(n : ℝ) := by positivity
      have hq : 0 ≤ y ^ (21 / 4 : ℝ) := by positivity
      nlinarith [abs_nonneg (Real.sin (th n y)), mul_le_mul hs this hq zero_le_one]
    calc _ ≤ |(23 / 4) * y ^ (23 / 4 - 1 : ℝ) * Real.cos (th n y)| +
          |y ^ (23 / 4 : ℝ) * (Real.sin (th n y) * (4 * π * √(n : ℝ) * (1 / (2 * √y))))| := abs_sub _ _
      _ ≤ 6 * Y ^ (21 / 4 : ℝ) + 2 * π * √(n : ℝ) * Y ^ (21 / 4 : ℝ) := add_le_add hA hB
      _ = (6 + 2 * π * √(n : ℝ)) * Y ^ (21 / 4 : ℝ) := by ring
  have := norm_image_sub_le_of_norm_deriv_le_segment' hd hb x' ⟨h2, le_rfl⟩
  rwa [Real.norm_eq_abs] at this


/-! ### Short sums in mean square -/

lemma card_Ioc_floor_le {x H : ℝ} (hx : 0 ≤ x) (hH : 0 ≤ H) :
    ((Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊).card : ℝ) ≤ H + 1 := by
  rw [Nat.card_Ioc]
  have hle : ⌊x⌋₊ ≤ ⌊x + H⌋₊ := Nat.floor_le_floor (by linarith)
  rw [Nat.cast_sub hle]
  have h1 : (⌊x + H⌋₊ : ℝ) ≤ x + H := Nat.floor_le (by linarith)
  have h2 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  linarith

lemma short_sq_pointwise {X H x : ℝ} (hX : 0 < X) (hH : 0 ≤ H) (hHX : H ≤ X)
    (hx : x ∈ Ioc X (2 * X)) :
    (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, |((tau n : ℤ) : ℝ)|) ^ 2 ≤
      (H + 1) * ∑ n ∈ Finset.Icc 1 ⌊3 * X⌋₊,
        ((tau n : ℤ) : ℝ) ^ 2 * (Ico ((n : ℝ) - H) n).indicator 1 x := by
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊)
    (f := fun n => |((tau n : ℤ) : ℝ)|)
  simp only [sq_abs] at hcs
  refine hcs.trans ?_
  have hsub : Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊ ⊆ Finset.Icc 1 ⌊3 * X⌋₊ := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.1 hn
    refine Finset.mem_Icc.2 ⟨by omega, h2.trans (Nat.floor_le_floor (by linarith [hx.2]))⟩
  have hind : ∀ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, (Ico ((n : ℝ) - H) n).indicator 1 x = (1 : ℝ) := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.1 hn
    have hxn : x < n := (Nat.floor_lt hx0).1 h1
    have hnx : (n : ℝ) ≤ x + H := by
      have := (Nat.le_floor_iff (by linarith)).1 h2; exact this
    rw [Set.indicator_of_mem (by constructor <;> linarith)]; rfl
  have hS : ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, ((tau n : ℤ) : ℝ) ^ 2 ≤
      ∑ n ∈ Finset.Icc 1 ⌊3 * X⌋₊, ((tau n : ℤ) : ℝ) ^ 2 * (Ico ((n : ℝ) - H) n).indicator 1 x := by
    calc ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, ((tau n : ℤ) : ℝ) ^ 2
        = ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, ((tau n : ℤ) : ℝ) ^ 2 * (Ico ((n : ℝ) - H) n).indicator 1 x :=
          Finset.sum_congr rfl fun n hn => by rw [hind n hn, mul_one]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by
          have : 0 ≤ (Ico ((n : ℝ) - H) n).indicator (1 : ℝ → ℝ) x :=
            Set.indicator_nonneg (fun _ _ => zero_le_one) x
          positivity)
  have hc := card_Ioc_floor_le hx0 hH
  have h0 : 0 ≤ ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, ((tau n : ℤ) : ℝ) ^ 2 :=
    Finset.sum_nonneg fun n _ => sq_nonneg _
  calc ((Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊).card : ℝ) * ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, ((tau n : ℤ) : ℝ) ^ 2
      ≤ (H + 1) * ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, ((tau n : ℤ) : ℝ) ^ 2 := by gcongr
    _ ≤ _ := by gcongr

/-- **Short sums in mean square**: `∫_X^{2X} (Σ_{x<n≤x+H} |τ(n)|)² ≤ (H+1) H Σ_{n≤3X} τ(n)²`. -/
theorem integral_short_sq_le {X H : ℝ} (hX : 0 < X) (hH : 0 ≤ H) (hHX : H ≤ X) :
    ∫ x in Ioc X (2 * X), (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, |((tau n : ℤ) : ℝ)|) ^ 2 ≤
      (H + 1) * H * ∑ n ∈ Finset.Icc 1 ⌊3 * X⌋₊, ((tau n : ℤ) : ℝ) ^ 2 := by
  set g : ℝ → ℝ := fun x => (H + 1) * ∑ n ∈ Finset.Icc 1 ⌊3 * X⌋₊,
    ((tau n : ℤ) : ℝ) ^ 2 * (Ico ((n : ℝ) - H) n).indicator 1 x with hg
  have hfin : ∀ n : ℕ, (volume.restrict (Ioc X (2 * X))) (Ico ((n : ℝ) - H) n) ≠ ⊤ := by
    intro n
    rw [Measure.restrict_apply measurableSet_Ico]
    exact ((measure_mono inter_subset_left).trans_lt measure_Ico_lt_top).ne
  have hgi : IntegrableOn g (Ioc X (2 * X)) := by
    refine Integrable.const_mul (integrable_finsetSum _ fun n _ => ?_) _
    refine Integrable.const_mul ?_ _
    exact (integrable_indicator_iff measurableSet_Ico).2 (integrableOn_const (hfin n) (by simp))
  have h1 := integral_mono_of_nonneg (μ := volume.restrict (Ioc X (2 * X)))
    (Eventually.of_forall fun x => sq_nonneg (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, |((tau n : ℤ) : ℝ)|)) hgi
    ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx =>
      short_sq_pointwise hX hH hHX hx))
  refine h1.trans ?_
  rw [hg, integral_const_mul, integral_finsetSum _ (fun n _ => Integrable.const_mul
    ((integrable_indicator_iff measurableSet_Ico).2 (integrableOn_const (hfin n) (by simp))) _),
    mul_assoc]
  gcongr
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [integral_const_mul, integral_indicator_one measurableSet_Ico,
    measureReal_restrict_apply measurableSet_Ico]
  have : volume.real (Ico ((n : ℝ) - H) n ∩ Ioc X (2 * X)) ≤ H := by
    calc volume.real (Ico ((n : ℝ) - H) n ∩ Ioc X (2 * X)) ≤ volume.real (Ico ((n : ℝ) - H) n) :=
          measureReal_mono inter_subset_left (by simp)
      _ = H := by rw [Real.volume_real_Ico_of_le (by linarith)]; ring
  rw [mul_comm H]
  exact mul_le_mul_of_nonneg_left this (sq_nonneg _)

end RamanujanTau.VoronoiTrunc
