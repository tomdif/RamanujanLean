/-
# Sign changes of τ in short intervals, from ANY Rankin–Selberg power saving

`tau_sign_change_short_interval_of_power_saving`: if
`|∑_{n≤N} τ(n)²/n¹¹ − c·N| ≤ C·N^{1−δ}` for all `N ≥ 1`, then for every window exponent `θ`
with `3/4 < θ ≤ 1` and `1 − δ ≤ θ` there are `A > 0`, `X₀` such that every `(x, x+h]` with
`x ≥ X₀`, `A·x^θ ≤ h ≤ x` contains `m, n` with `τ(m) > 0 > τ(n)`.

Same proof as `Window.lean`, with `83/84` replaced by `θ` and `ε := (θ − 3/4)/4`:
Hecke × Weil give `∑_W τ²/n¹¹ ≪ x^{3/4+2ε}` on a one-signed window, Rankin–Selberg gives
`≥ c h − O(x^θ)`, and `θ − (3/4 + 2ε) = (θ − 3/4)/2 > 0`.
So the optimal window exponent is `θ = max(1 − δ, 3/4 + ε)`: the RS exponent is the
bottleneck exactly when `δ < 1/4`.
-/
import RamanujanTau.TauSigns.Window

set_option autoImplicit false

namespace RamanujanTau.TauSigns

open Finset Filter Asymptotics
open scoped Real

/-- **Sign changes in short intervals, parametrized by the RS power saving `δ`.** -/
theorem tau_sign_change_short_interval_of_power_saving {δ θ : ℝ} (hθ : 3 / 4 < θ) (hθ1 : θ ≤ 1)
    (hδθ : 1 - δ ≤ θ)
    (hRS : ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 -
          3 / π * (4 * π) ^ 12 * EisensteinReal.petNormSq / (Nat.factorial 11 : ℝ) * N| ≤
        C * (N : ℝ) ^ (1 - δ)) :
    ∃ A X₀ : ℝ, 0 < A ∧ ∀ x h : ℕ, X₀ ≤ x → A * (x : ℝ) ^ θ ≤ h → h ≤ x →
      (∃ m ∈ Ioc x (x + h), 0 < tau m) ∧ (∃ n ∈ Ioc x (x + h), tau n < 0) := by
  set ε : ℝ := (θ - 3 / 4) / 4
  have hε0 : 0 < ε := by simp only [ε]; linarith
  have hε1 : ε ≤ 1 / 16 := by simp only [ε]; linarith
  obtain ⟨CH, hCH⟩ := hecke_partial_sum (ε := ε) hε0 (by linarith)
  obtain ⟨D, hD⟩ := (StepanovAS.tau_isBigO_23_4_unconditional ε hε0).bound
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hD
  obtain ⟨CR₀, hCR₀⟩ := hRS
  set CR := max CR₀ 0
  have hCR : ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 -
          3 / π * (4 * π) ^ 12 * EisensteinReal.petNormSq / (Nat.factorial 11 : ℝ) * N| ≤
        CR * (N : ℝ) ^ θ := by
    intro N hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    refine le_trans (hCR₀ N hN) ?_
    calc CR₀ * (N : ℝ) ^ (1 - δ) ≤ CR * (N : ℝ) ^ (1 - δ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) _)
      _ ≤ CR * (N : ℝ) ^ θ :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 hδθ) (le_max_right _ _)

  set c : ℝ := 3 / π * (4 * π) ^ 12 * EisensteinReal.petNormSq / (Nat.factorial 11 : ℝ)
  have hc : 0 < c := by
    have := RankinError.petNormSq_pos; have := Real.pi_pos; positivity
  set CR' := max CR 0
  set CH' := max CH 0
  set D' := max D 0
  set K : ℝ := 64 * D' * (129 * CH')
  set A : ℝ := (3 * CR' + 1) / c
  have hA : 0 < A := by positivity
  set β : ℝ := 3 / 4 + 2 * ε
  set δ' : ℝ := θ - β
  have hδ : 0 < δ' := by simp only [δ', β, ε]; linarith
  have htend : Tendsto (fun x : ℕ => (x : ℝ) ^ δ') atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp (htend.eventually_gt_atTop K)
  refine ⟨A, max (max n₀ X₁) 1, hA, ?_⟩
  intro x h hx hAh hhx
  have hxn₀ : n₀ ≤ x := by
    have : ((n₀ : ℕ) : ℝ) ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
    exact_mod_cast this
  have hxX₁ : X₁ ≤ x := by
    have : ((X₁ : ℕ) : ℝ) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
    exact_mod_cast this
  have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hx1n : 1 ≤ x := by exact_mod_cast hx1
  have hxpos : (0 : ℝ) < x := by linarith
  have hxh2 : ((x + h : ℕ) : ℝ) ≤ 2 * x := by
    have : (h : ℝ) ≤ x := by exact_mod_cast hhx
    push_cast; linarith
  -- the core: no sign on the window is impossible
  suffices key : ∀ s : ℤ, (s = 1 ∨ s = -1) → ¬ ∀ n ∈ Ioc x (x + h), 0 ≤ s * tau n by
    constructor
    · by_contra hneg
      push Not at hneg
      exact key (-1) (Or.inr rfl) fun n hn => by have := hneg n hn; linarith
    · by_contra hneg
      push Not at hneg
      exact key 1 (Or.inl rfl) fun n hn => by have := hneg n hn; linarith
  intro s hs hsign
  have hsA : |(s : ℝ)| = 1 := by rcases hs with rfl | rfl <;> simp
  set W := Ioc x (x + h)
  -- (iv) sum of |τ| over the window
  have habs : ∑ n ∈ W, |(tau n : ℝ)| = |∑ n ∈ W, (tau n : ℝ)| := by
    have e : ∀ n ∈ W, |(tau n : ℝ)| = (s : ℝ) * (tau n : ℝ) := by
      intro n hn
      have h0 : (0 : ℝ) ≤ (s : ℝ) * (tau n : ℝ) := by exact_mod_cast hsign n hn
      rw [← abs_of_nonneg h0, abs_mul, hsA, one_mul]
    have hnn : 0 ≤ ∑ n ∈ W, (s : ℝ) * (tau n : ℝ) :=
      sum_nonneg fun n hn => by exact_mod_cast hsign n hn
    rw [sum_congr rfl e, ← mul_sum] at *
    rw [show |∑ n ∈ W, (tau n : ℝ)| = |(s : ℝ) * ∑ n ∈ W, (tau n : ℝ)| by
      rw [abs_mul, hsA, one_mul], abs_of_nonneg hnn]
  have hT : ∀ N : ℕ, 1 ≤ N → |∑ n ∈ Ioc 0 N, (tau n : ℝ)| ≤ CH' * (N : ℝ) ^ (6 + ε) := by
    intro N hN
    have := hCH N hN
    rw [sum_range_succ_eq, tau_zero] at this
    simp only [Int.cast_zero, zero_add] at this
    exact le_trans this (by gcongr; exact le_max_left _ _)
  have hq : (0 : ℝ) ≤ 6 + ε := by linarith
  have hsumabs : ∑ n ∈ W, |(tau n : ℝ)| ≤ 129 * CH' * (x : ℝ) ^ (6 + ε) := by
    rw [habs, sum_Ioc_window]
    have h1 := hT (x + h) (by omega)
    have h2 := hT x hx1n
    have h3 : ((x + h : ℕ) : ℝ) ^ (6 + ε) ≤ 128 * (x : ℝ) ^ (6 + ε) := by
      calc ((x + h : ℕ) : ℝ) ^ (6 + ε) ≤ (2 * (x : ℝ)) ^ (6 + ε) :=
            Real.rpow_le_rpow (by positivity) hxh2 hq
        _ ≤ 128 * (x : ℝ) ^ (6 + ε) :=
            two_mul_rpow_le hxpos.le hq (by
              have := two_rpow_le (p := 6 + ε) (k := 7) (by push_cast; linarith); norm_num at this ⊢
              linarith)
    have hCH0 : 0 ≤ CH' := le_max_right _ _
    calc |∑ n ∈ Ioc 0 (x + h), (tau n : ℝ) - ∑ n ∈ Ioc 0 x, (tau n : ℝ)|
        ≤ |∑ n ∈ Ioc 0 (x + h), (tau n : ℝ)| + |∑ n ∈ Ioc 0 x, (tau n : ℝ)| := abs_sub _ _
      _ ≤ CH' * (128 * (x : ℝ) ^ (6 + ε)) + CH' * (x : ℝ) ^ (6 + ε) := by
          gcongr
          · exact le_trans h1 (mul_le_mul_of_nonneg_left h3 hCH0)
      _ = 129 * CH' * (x : ℝ) ^ (6 + ε) := by ring
  -- (iii) Weil bound on the window
  have hp : (0 : ℝ) ≤ 23 / 4 + ε := by linarith
  have hweil : ∀ n ∈ W, |(tau n : ℝ)| ≤ 64 * D' * (x : ℝ) ^ (23 / 4 + ε) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := mem_Ioc.mp hn
    have h := hn₀ n (by omega)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] at h
    have hn2' : (n : ℝ) ≤ 2 * x := le_trans (by exact_mod_cast hn2) hxh2
    calc |(tau n : ℝ)| ≤ D * (n : ℝ) ^ (23 / 4 + ε) := h
      _ ≤ D' * (2 * (x : ℝ)) ^ (23 / 4 + ε) := by
          apply mul_le_mul (le_max_left _ _) (Real.rpow_le_rpow (Nat.cast_nonneg _) hn2' hp)
            (Real.rpow_nonneg (Nat.cast_nonneg _) _) (le_max_right _ _)
      _ ≤ D' * (64 * (x : ℝ) ^ (23 / 4 + ε)) := by
          apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
          exact two_mul_rpow_le hxpos.le hp (by
            have := two_rpow_le (p := 23 / 4 + ε) (k := 6) (by push_cast; linarith); norm_num at this ⊢
            linarith)
      _ = 64 * D' * (x : ℝ) ^ (23 / 4 + ε) := by ring
  have hsq : ∑ n ∈ W, (tau n : ℝ) ^ 2 ≤ K * (x : ℝ) ^ (23 / 4 + ε) * (x : ℝ) ^ (6 + ε) := by
    calc ∑ n ∈ W, (tau n : ℝ) ^ 2 = ∑ n ∈ W, |(tau n : ℝ)| * |(tau n : ℝ)| := by
          refine sum_congr rfl fun n _ => ?_; rw [← sq, sq_abs]
      _ ≤ ∑ n ∈ W, 64 * D' * (x : ℝ) ^ (23 / 4 + ε) * |(tau n : ℝ)| :=
          sum_le_sum fun n hn => mul_le_mul_of_nonneg_right (hweil n hn) (abs_nonneg _)
      _ = 64 * D' * (x : ℝ) ^ (23 / 4 + ε) * ∑ n ∈ W, |(tau n : ℝ)| := by rw [mul_sum]
      _ ≤ 64 * D' * (x : ℝ) ^ (23 / 4 + ε) * (129 * CH' * (x : ℝ) ^ (6 + ε)) := by
          apply mul_le_mul_of_nonneg_left hsumabs
          have : 0 ≤ D' := le_max_right _ _
          positivity
      _ = K * (x : ℝ) ^ (23 / 4 + ε) * (x : ℝ) ^ (6 + ε) := by simp only [K]; ring
  -- (ii) τ²/n¹¹ ≤ τ²/x¹¹ on the window
  have hdiv : ∑ n ∈ W, (tau n : ℝ) ^ 2 / (n : ℝ) ^ 11 ≤
      (∑ n ∈ W, (tau n : ℝ) ^ 2) / (x : ℝ) ^ 11 := by
    rw [sum_div]
    refine sum_le_sum fun n hn => ?_
    have hn1 : (x : ℝ) ≤ n := by exact_mod_cast (mem_Ioc.mp hn).1.le
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    exact pow_le_pow_left₀ hxpos.le hn1 11
  -- (i) Rankin–Selberg on the window
  have hRS : c * h - 3 * CR' * (x : ℝ) ^ θ ≤ ∑ n ∈ W, (tau n : ℝ) ^ 2 / (n : ℝ) ^ 11 := by
    have e := sum_Ioc_window (fun n => (tau n : ℝ) ^ 2 / (n : ℝ) ^ 11) x h
    simp only at e
    rw [e, ← Icc_one_eq_Ioc, ← Icc_one_eq_Ioc]
    have h1 := hCR (x + h) (by omega)
    have h2 := hCR x hx1n
    have ha : (0 : ℝ) ≤ θ := by linarith
    have h3 : ((x + h : ℕ) : ℝ) ^ θ ≤ 2 * (x : ℝ) ^ θ := by
      calc ((x + h : ℕ) : ℝ) ^ θ ≤ (2 * (x : ℝ)) ^ θ :=
            Real.rpow_le_rpow (by positivity) hxh2 ha
        _ ≤ 2 * (x : ℝ) ^ θ :=
            two_mul_rpow_le hxpos.le ha (by
              have := two_rpow_le (p := θ) (k := 1) (by push_cast; linarith); norm_num at this ⊢
              linarith)
    have hCR0 : 0 ≤ CR' := le_max_right _ _
    have h1' : CR * ((x + h : ℕ) : ℝ) ^ θ ≤ CR' * (2 * (x : ℝ) ^ θ) := by
      exact le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) _))
        (mul_le_mul_of_nonneg_left h3 hCR0)
    have h2' : CR * (x : ℝ) ^ θ ≤ CR' * (x : ℝ) ^ θ := by
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) _)
    have hab1 := (abs_le.mp h1).1
    have hab2 := (abs_le.mp h2).2
    have hlin : c * ((x + h : ℕ) : ℝ) = c * x + c * h := by push_cast; ring
    linarith
  -- combine
  have hx11 : (x : ℝ) ^ (23 / 4 + ε) * (x : ℝ) ^ (6 + ε) / (x : ℝ) ^ 11 = (x : ℝ) ^ β := by
    rw [← Real.rpow_add hxpos, ← Real.rpow_natCast, ← Real.rpow_sub hxpos]
    congr 1; simp only [β]; push_cast; ring
  have hmain : c * h - 3 * CR' * (x : ℝ) ^ θ ≤ K * (x : ℝ) ^ β := by
    calc c * h - 3 * CR' * (x : ℝ) ^ θ ≤ (∑ n ∈ W, (tau n : ℝ) ^ 2) / (x : ℝ) ^ 11 :=
          le_trans hRS hdiv
      _ ≤ K * (x : ℝ) ^ (23 / 4 + ε) * (x : ℝ) ^ (6 + ε) / (x : ℝ) ^ 11 :=
          div_le_div_of_nonneg_right hsq (by positivity)
      _ = K * (x : ℝ) ^ β := by rw [mul_assoc, mul_div_assoc, hx11]
  have hch : (3 * CR' + 1) * (x : ℝ) ^ θ ≤ c * h := by
    have := mul_le_mul_of_nonneg_left hAh hc.le
    calc (3 * CR' + 1) * (x : ℝ) ^ θ = c * (A * (x : ℝ) ^ θ) := by
          simp only [A]; field_simp
      _ ≤ c * h := this
  have hsplit : (x : ℝ) ^ θ = (x : ℝ) ^ δ' * (x : ℝ) ^ β := by
    rw [← Real.rpow_add hxpos]; congr 1; simp only [δ']; ring
  have hbig := hX₁ x hxX₁
  have h1720 : 0 < (x : ℝ) ^ β := Real.rpow_pos_of_pos hxpos _
  have : (x : ℝ) ^ δ' * (x : ℝ) ^ β ≤ K * (x : ℝ) ^ β := by
    rw [← hsplit]; linarith
  have := le_of_mul_le_mul_right this h1720
  linarith

end RamanujanTau.TauSigns

#print axioms RamanujanTau.TauSigns.tau_sign_change_short_interval_of_power_saving
