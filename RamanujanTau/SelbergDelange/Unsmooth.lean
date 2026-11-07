/-
# The Rankin–Selberg prime number theorem with de la Vallée-Poussin error term

`ψ_R(x) = Σ_{n≤x} vR(n)`, where `vR(p^k) = (α_p^k + β_p^k)² log p ≥ 0` is the von Mangoldt
function of `ζ(2s)R(s) = L(Δ×Δ,s)` (so `vR(p) = λ(p)² log p`).

**Theorem** (`psiR_error`, unconditional, Deligne-free).
`|ψ_R(x) − x| ≤ K x exp(−b√log x)` for `x ≥ X₀`.

Unsmoothing is elementary because `vR ≥ 0`: with `F(x) = Σ_{n≤x} vR(n)(x−n)`,
`h ψ_R(x) ≤ F(x+h) − F(x) ≤ h ψ_R(x+h)` (`diff_sandwich`), and `F(x) = (x−1)²/2 + O(x²e^{−a√log x})`
(`FR_bound`, from `smoothed_boundK`).  Take `h = x exp(−(a/4)√log x)`.
-/
import RamanujanTau.SelbergDelange.Smoothed

set_option autoImplicit false

namespace RamanujanTau.SelbergDelange

open Complex Filter Topology
open RamanujanTau.EdgeNonvanishing RamanujanTau.TauPNTUncond RamanujanTau.RankinError
open RamanujanTau.TauPartialSums

/-- `ψ_R(x) = Σ_{n≤x} vR(n)`. -/
noncomputable def psiR (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vR n

/-- `F(x) = Σ_{n≤x} vR(n)(x − n)`. -/
noncomputable def FR (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vR n * (x - n)

lemma F1_vR_eq (x : ℝ) : F1 (fun n => (vR n : ℂ)) x = (FR x : ℂ) := by
  simp [F1, FR]

lemma A_vR_eq (x : ℝ) : A (fun n => (vR n : ℂ)) x = (psiR x : ℂ) := by
  simp [A, psiR]

/-- `|F(x) − (x−1)²/2| ≤ K x² exp(−a√log x)`. -/
theorem FR_bound : ∃ a : ℝ, 0 < a ∧ a ≤ 1 / 64 ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 3 ≤ x →
    |FR x - (x - 1) ^ 2 / 2| ≤ K * x ^ 2 * Real.exp (-a * Real.sqrt (Real.log x)) := by
  obtain ⟨a, ha, ha64, K, hK, h⟩ := smoothed_boundK
  refine ⟨a, ha, ha64, K, hK, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have ht := tsum_phi_eq (fun n => (vR n : ℂ)) vR_zero' hx0
  rw [F1_vR_eq] at ht
  have e : ((FR x - (x - 1) ^ 2 / 2 : ℝ) : ℂ) = (x : ℂ) * (∑' n : ℕ, (vR n : ℂ) * (phi 1 (n / x) : ℂ) -
      ((x * (1 - 1 / x) ^ 2 / 2 : ℝ) : ℂ)) := by
    rw [mul_sub, ht]
    have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    push_cast
    field_simp
  have hn := congrArg norm e
  rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hx0] at hn
  rw [hn]
  calc x * ‖∑' n : ℕ, (vR n : ℂ) * (phi 1 (n / x) : ℂ) - ((x * (1 - 1 / x) ^ 2 / 2 : ℝ) : ℂ)‖
      ≤ x * (K * x * Real.exp (-a * Real.sqrt (Real.log x))) := by gcongr; exact h x hx
    _ = _ := by ring

lemma vR_nonneg' (n : ℕ) : 0 ≤ vR n := vR_nonneg n

/-- **The differencing sandwich** for the non-negative `vR`. -/
theorem diff_sandwich {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) :
    h * psiR x ≤ FR (x + h) - FR x ∧ FR (x + h) - FR x ≤ h * psiR (x + h) := by
  have hd := F1_diff (fun n => (vR n : ℂ)) hx hh
  rw [F1_vR_eq, F1_vR_eq, A_vR_eq] at hd
  set S : ℝ := ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, vR n * ((x + h) - n) with hS
  have hd' : FR (x + h) - FR x = h * psiR x + S := by
    have : ((FR (x + h) - FR x : ℝ) : ℂ) = ((h * psiR x + S : ℝ) : ℂ) := by
      push_cast; rw [hd, hS]; push_cast; rfl
    exact_mod_cast this
  have hNM : ⌊x⌋₊ ≤ ⌊x + h⌋₊ := Nat.floor_le_floor (by linarith)
  have hpsi : psiR (x + h) = psiR x + ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, vR n := by
    simp only [psiR, Icc_one_eq_Ioc]
    rw [Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hNM]
  have hterm : ∀ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, 0 ≤ vR n * ((x + h) - n) ∧
      vR n * ((x + h) - n) ≤ h * vR n := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.1 hn
    have hup : (n : ℝ) ≤ x + h :=
      (Nat.cast_le.2 h2).trans (Nat.floor_le (by linarith))
    have hlow : x < n := by
      have := Nat.lt_floor_add_one x
      have : (⌊x⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast h1
      linarith
    have hv := vR_nonneg n
    exact ⟨mul_nonneg hv (by linarith), by nlinarith⟩
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun n hn => (hterm n hn).1
  have hS1 : S ≤ h * ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, vR n := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun n hn => (hterm n hn).2
  constructor
  · linarith
  · rw [hd', hpsi]; nlinarith

lemma exp_sqrt_anti {a y x : ℝ} (ha : 0 ≤ a) (hy : 1 ≤ y) (hxy : y ≤ x) :
    Real.exp (-a * Real.sqrt (Real.log x)) ≤ Real.exp (-a * Real.sqrt (Real.log y)) := by
  apply Real.exp_le_exp.mpr
  have : Real.sqrt (Real.log y) ≤ Real.sqrt (Real.log x) :=
    Real.sqrt_le_sqrt (Real.log_le_log (by linarith) hxy)
  nlinarith

set_option maxHeartbeats 2000000 in
/-- **Rankin–Selberg PNT with de la Vallée-Poussin error term** (unconditional, no Deligne):
`|Σ_{n≤x} vR(n) − x| ≤ K x exp(−b√log x)` for `x ≥ X₀`. -/
theorem psiR_error : ∃ b : ℝ, 0 < b ∧ ∃ K X₀ : ℝ, 0 ≤ K ∧ ∀ x : ℝ, X₀ ≤ x →
    |psiR x - x| ≤ K * x * Real.exp (-b * Real.sqrt (Real.log x)) := by
  obtain ⟨a, ha, ha64, K, hK, hF⟩ := FR_bound
  refine ⟨a / 4, by positivity, 3 / 2 + 8 * K, max 6 (Real.exp ((4 / a) ^ 2)), by positivity,
    fun x hx => ?_⟩
  have hx6 : 6 ≤ x := le_trans (le_max_left _ _) hx
  have hxE : Real.exp ((4 / a) ^ 2) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  have hlogx : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; have := Real.exp_one_lt_d9; linarith
  set ℓ := Real.sqrt (Real.log x) with hℓ
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ, show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hlogx
  have hℓa : 4 / a ≤ ℓ := by
    rw [hℓ]
    have : (4 / a) ^ 2 ≤ Real.log x := by
      rw [Real.le_log_iff_exp_le hx0]; exact hxE
    calc 4 / a = Real.sqrt ((4 / a) ^ 2) := by rw [Real.sqrt_sq (by positivity)]
      _ ≤ _ := Real.sqrt_le_sqrt this
  set r : ℝ := Real.exp (-(a / 4) * ℓ) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr2 : r ≤ 1 / 2 := by
    have h1 : -(a / 4) * ℓ ≤ -1 := by
      have : a / 4 * ℓ ≥ a / 4 * (4 / a) := by gcongr
      have e : a / 4 * (4 / a) = 1 := by field_simp
      nlinarith
    have := Real.exp_le_exp.mpr h1
    have h2 : Real.exp (-1) < 1 / 2 := by
      rw [Real.exp_neg]; have := Real.exp_one_gt_d9
      rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]; linarith
    linarith
  have hxr : 1 ≤ x * r := by
    have h1 : Real.exp (Real.log x - (a / 4) * ℓ) = x * r := by
      rw [Real.exp_sub, Real.exp_log hx0, hr, neg_mul, Real.exp_neg]; ring
    rw [← h1]
    apply Real.one_le_exp
    have : ℓ ≤ Real.log x := by
      rw [hℓ]
      calc Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log x) * Real.sqrt (Real.log x) := by
            have := Real.sqrt_nonneg (Real.log x); nlinarith
        _ = Real.log x := Real.mul_self_sqrt (by linarith)
    nlinarith
  set h : ℝ := x * r with hhdef
  have hh0 : 0 < h := by positivity
  have hhx : h ≤ x / 2 := by rw [hhdef]; nlinarith
  -- the error at the three points
  have hεy : ∀ y : ℝ, x / 2 ≤ y → y ≤ 2 * x →
      |FR y - (y - 1) ^ 2 / 2| ≤ 4 * K * x ^ 2 * r ^ 2 := by
    intro y hy1 hy2
    have hy3 : 3 ≤ y := by linarith
    have hy0 : 0 < y := by linarith
    refine (hF y hy3).trans ?_
    have hlog : Real.log x / 4 ≤ Real.log y := by
      have h1 : Real.log (x / 2) ≤ Real.log y := Real.log_le_log (by linarith) hy1
      rw [Real.log_div hx0.ne' (by norm_num)] at h1
      have := Real.log_two_lt_d9
      linarith
    have hsq : ℓ / 2 ≤ Real.sqrt (Real.log y) := by
      rw [hℓ]
      calc Real.sqrt (Real.log x) / 2 = Real.sqrt (Real.log x / 4) := by
            rw [Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4)]
            rw [show Real.sqrt 4 = 2 by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)]
        _ ≤ _ := Real.sqrt_le_sqrt hlog
    have he : Real.exp (-a * Real.sqrt (Real.log y)) ≤ r ^ 2 := by
      rw [hr, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      push_cast
      nlinarith
    have hy2' : y ^ 2 ≤ 4 * x ^ 2 := by nlinarith
    calc K * y ^ 2 * Real.exp (-a * Real.sqrt (Real.log y)) ≤ K * (4 * x ^ 2) * r ^ 2 := by
          gcongr
      _ = _ := by ring
  have e1 := hεy x (by linarith) (by linarith)
  have e2 := hεy (x + h) (by linarith) (by linarith)
  have e3 := hεy (x - h) (by linarith) (by linarith)
  obtain ⟨s1, s2⟩ := diff_sandwich (x := x) (h := h) hx0.le hh0.le
  obtain ⟨s3, s4⟩ := diff_sandwich (x := x - h) (h := h) (by linarith) hh0.le
  rw [sub_add_cancel] at s3 s4
  have hrh : h * (8 * K * x * r) = 8 * K * x ^ 2 * r ^ 2 := by rw [hhdef]; ring
  rw [abs_le] at e1 e2 e3
  have up : h * psiR x ≤ h * (x - 1 + h / 2 + 8 * K * x * r) := by
    rw [mul_add, hrh]; nlinarith [e1.1, e1.2, e2.1, e2.2]
  have lo : h * (x - 1 - h / 2 - 8 * K * x * r) ≤ h * psiR x := by
    have : h * (x - 1 - h / 2 - 8 * K * x * r) = h * (x - 1) - h ^ 2 / 2 - 8 * K * x ^ 2 * r ^ 2 := by
      rw [mul_sub, hrh]; ring
    rw [this]; nlinarith [e1.1, e1.2, e3.1, e3.2]
  have up' := le_of_mul_le_mul_left up hh0
  have lo' := le_of_mul_le_mul_left lo hh0
  have hfin : |psiR x - x| ≤ (3 / 2 + 8 * K) * (x * r) := by
    rw [abs_le]; constructor <;> nlinarith
  have hrr : r = Real.exp (-(a / 4) * Real.sqrt (Real.log x)) := by rw [hr, hℓ]
  rw [hrr] at hfin
  linarith [hfin]

end RamanujanTau.SelbergDelange
