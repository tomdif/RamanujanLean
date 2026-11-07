/-
# GORZ Theorem 3 through forward differences, and differences from derivatives

* **`gorz_thm3_diff`** : if `α > 0`, `δ > 0`, `δ → 0`, `Δ²[log α](n)/δ(n)² → −2` and
  `Δ^k[log α](n)/δ(n)^k → 0` for `3 ≤ k ≤ d` (`Δ^k[log α](n) = Σ_j (−1)^{k−j} C(k,j) log α(n+j)`), then with
  `E(n) = α(n+1)/α(n)` the renormalized Jensen polynomials converge to `H_d` (coefficientwise and uniformly
  on compacts) and `J^{d,n}_α` is eventually hyperbolic.  Proof: by Newton interpolation
  `log(α(n+j)/α(n)) − j log E(n) = Σ_{k=2}^{d} Δ^k[log α](n) C(j,k) = Q_n(δj)` exactly, with
  `Q_n(y) = Σ_k Δ^k[log α](n)/k! · (y/δ)^{\underline k}`, whose coefficients converge to those of `−y²`.
* **`fd_chain_close`** : for a derivative chain `G 0, G 1, …` on `[0, ∞)`,
  `|Δ^K[G 0](0) − G K (0)| ≤ 2^K K^{K+1} sup_{[0,K]} |G (K+1)|` (Taylor to order `K+1`).
-/
import RamanujanTau.GORZXi.Theorem3

set_option autoImplicit false

namespace GORZXi

open Real Finset Filter Topology Polynomial Asymptotics JensenThreshold

/-- `Δ^k[log α](n)`. -/
noncomputable def dlog (α : ℕ → ℝ) (n k : ℕ) : ℝ := GORZ.fd (fun j => Real.log (α (n + j))) k

lemma fd_zero (w : ℕ → ℝ) : GORZ.fd w 0 = w 0 := by simp [GORZ.fd]
lemma fd_one (w : ℕ → ℝ) : GORZ.fd w 1 = w 1 - w 0 := by
  simp [GORZ.fd, Finset.sum_range_succ]; ring

/-- the Newton polynomial `Q_n(y) = Σ_{k=2}^{D'} f_k/k! · desc_k(y/δ)`, `D' = max d 2`. -/
noncomputable def Qd (α δ : ℕ → ℝ) (d n : ℕ) : ℝ[X] :=
  ∑ k ∈ range (max d 2 - 1), C (dlog α n (k + 2) / ((k + 2).factorial : ℝ)) *
    (descPochhammer ℝ (k + 2)).comp (C (δ n)⁻¹ * X)

lemma descPoch_coeff_self (m : ℕ) : (descPochhammer ℝ m).coeff m = 1 := by
  have h := monic_descPochhammer ℝ m
  rw [Monic, leadingCoeff, descPochhammer_natDegree] at h
  exact h

lemma descPoch_coeff_gt {k m : ℕ} (h : k < m) : (descPochhammer ℝ k).coeff m = 0 :=
  coeff_eq_zero_of_natDegree_lt (by rw [descPochhammer_natDegree]; exact h)

theorem gorz_thm3_diff (α δ : ℕ → ℝ) (d : ℕ) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hδpos : ∀ᶠ n in atTop, 0 < δ n) (hαpos : ∀ᶠ n in atTop, 0 < α n)
    (h2 : Tendsto (fun n => dlog α n 2 / δ n ^ 2) atTop (𝓝 (-2)))
    (hk : ∀ k ∈ Icc 3 d, Tendsto (fun n => dlog α n k / δ n ^ k) atTop (𝓝 0)) :
    (∀ i, Tendsto (fun n => (Jhat α (fun n => α (n + 1) / α n) δ d n).coeff i) atTop
      (𝓝 ((GORZ.H d).coeff i))) ∧
    (∀ K : Set ℝ, IsCompact K → TendstoUniformlyOn
      (fun n x => (Jhat α (fun n => α (n + 1) / α n) δ d n).eval x) (fun x => (GORZ.H d).eval x) atTop K) ∧
    (∀ᶠ n in atTop, Hyperbolic (jensenSeq α d n)) := by
  have hδne : ∀ᶠ n in atTop, δ n ≠ 0 := hδpos.mono fun n h => h.ne'
  obtain ⟨D', hD'⟩ : ∃ D', D' = max d 2 := ⟨_, rfl⟩
  have hD2 : 2 ≤ D' := hD' ▸ le_max_right _ _
  have hdD : d ≤ D' := hD' ▸ le_max_left _ _
  have hDd : D' = d ∨ D' = 2 := by
    rcases le_total d 2 with h | h
    · right; rw [hD', max_eq_right h]
    · left; rw [hD', max_eq_left h]
  set A : ℕ → ℝ := fun n => Real.log (α (n + 1) / α n) with hA
  -- limits `ℓ`
  set ℓ : ℕ → ℝ := fun m => if m = 2 then -2 else 0 with hℓ
  have hlimk : ∀ k ∈ range (D' - 1), Tendsto (fun n => dlog α n (k + 2) / δ n ^ (k + 2)) atTop
      (𝓝 (ℓ (k + 2))) := by
    intro k hk'
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0; simpa [hℓ] using h2
    · have : k + 2 ∈ Icc 3 d := by
        simp only [mem_Icc, mem_range] at hk' ⊢
        omega
      rw [hℓ]; simp only [show k + 2 ≠ 2 by omega, if_false]
      exact hk (k + 2) this
  -- degree, constant term, coefficients
  have hdeg : ∀ n, (Qd α δ d n).natDegree ≤ D' := by
    intro n
    refine natDegree_sum_le_of_forall_le _ _ fun k hk' => ?_
    refine (natDegree_C_mul_le _ _).trans (natDegree_comp_le.trans ?_)
    rw [descPochhammer_natDegree]
    have h1 : (C (δ n)⁻¹ * X : ℝ[X]).natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans (by simp)
    have : k + 2 ≤ D' := by rw [← hD'] at hk'; simp only [mem_range] at hk'; omega
    calc (k + 2) * (C (δ n)⁻¹ * X : ℝ[X]).natDegree ≤ (k + 2) * 1 := Nat.mul_le_mul_left _ h1
      _ ≤ D' := by omega
  have hcoeff : ∀ n m, (Qd α δ d n).coeff m = ∑ k ∈ range (D' - 1),
      dlog α n (k + 2) / ((k + 2).factorial : ℝ) * ((descPochhammer ℝ (k + 2)).coeff m * (δ n)⁻¹ ^ m) := by
    intro n m
    simp only [Qd, hD', finsetSum_coeff, coeff_C_mul, comp_C_mul_X_coeff]
  have h0 : ∀ᶠ n in atTop, (Qd α δ d n).coeff 0 = 0 := Eventually.of_forall fun n => by
    rw [hcoeff]
    refine sum_eq_zero fun k _ => ?_
    simp [coeff_zero_eq_eval_zero]
  have hQ : CoeffTo (Qd α δ d) (-X ^ 2) := by
    intro m
    simp_rw [hcoeff]
    have hterm : ∀ k ∈ range (D' - 1), Tendsto (fun n => dlog α n (k + 2) / ((k + 2).factorial : ℝ) *
        ((descPochhammer ℝ (k + 2)).coeff m * (δ n)⁻¹ ^ m)) atTop
        (𝓝 (if m = k + 2 then ℓ (k + 2) / ((k + 2).factorial : ℝ) else 0)) := by
      intro k hk'
      rcases lt_or_ge (k + 2) m with hlt | hge
      · rw [if_neg (by omega)]
        simp [descPoch_coeff_gt hlt]
      · have h3 := ((hlimk k hk').mul (hδ0.pow (k + 2 - m))).div_const ((k + 2).factorial : ℝ) |>.mul_const
          ((descPochhammer ℝ (k + 2)).coeff m)
        have e : ∀ᶠ n in atTop, dlog α n (k + 2) / δ n ^ (k + 2) * δ n ^ (k + 2 - m) /
            ((k + 2).factorial : ℝ) * (descPochhammer ℝ (k + 2)).coeff m =
            dlog α n (k + 2) / ((k + 2).factorial : ℝ) * ((descPochhammer ℝ (k + 2)).coeff m * (δ n)⁻¹ ^ m) := by
          filter_upwards [hδne] with n hn
          have : δ n ^ (k + 2) = δ n ^ m * δ n ^ (k + 2 - m) := by rw [← pow_add]; congr 1; omega
          rw [this, inv_pow]
          field_simp
        refine (h3.congr' e).trans ?_ |> fun h => h
        split_ifs with hm
        · subst hm; simp [descPoch_coeff_self]
        · rw [zero_pow (by omega)]; simp
    have hsum := tendsto_finsetSum _ hterm
    convert hsum using 2
    -- the limit coefficient
    simp only [coeff_neg, coeff_X_pow]
    by_cases hm : m = 2
    · subst hm
      rw [Finset.sum_eq_single 0]
      · simp [hℓ, Nat.factorial]
      · intro b _ hb; rw [if_neg (by omega)]
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    · rw [if_neg hm, neg_zero]
      symm
      refine sum_eq_zero fun k _ => ?_
      split_ifs with h
      · simp [hℓ, show k + 2 ≠ 2 by omega] at *
        omega
      · rfl
  -- the exact Newton expansion
  have hφ : ∀ j ≤ d, (fun n => Real.log (α (n + j) / α n) - A n * j - (Qd α δ d n).eval (δ n * j))
      =o[atTop] (fun n => δ n ^ d) := by
    intro j hj
    refine (isLittleO_zero (fun n => δ n ^ d) atTop).congr' ?_ EventuallyEq.rfl
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hαpos.and hδne)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hα0 := (hN n hn).1
    have hδn := (hN n hn).2
    have hpos : ∀ i, 0 < α (n + i) := fun i => (hN (n + i) (by omega)).1
    set w : ℕ → ℝ := fun i => Real.log (α (n + i)) with hw
    have hnew := GORZ.gregory_newton w (show j ≤ D' by omega)
    rw [show D' + 1 = (D' - 1) + 1 + 1 by omega, Finset.sum_range_succ', Finset.sum_range_succ'] at hnew
    have hev : (Qd α δ d n).eval (δ n * j) = ∑ k ∈ range (D' - 1), (j.choose (k + 2) : ℝ) * GORZ.fd w (k + 2) := by
      simp only [Qd, hD', eval_finsetSum, eval_mul, eval_C, eval_comp, eval_X]
      refine sum_congr rfl fun k _ => ?_
      rw [show (δ n)⁻¹ * (δ n * j) = (j : ℝ) by field_simp, descPochhammer_eval_eq_descFactorial,
        Nat.descFactorial_eq_factorial_mul_choose]
      simp only [dlog, hw]
      push_cast
      field_simp
    rw [hev]
    simp only [Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one, one_mul, fd_zero, fd_one,
      zero_add] at hnew
    have hw0 : w 0 = Real.log (α n) := by simp [hw]
    have hwj : w j = Real.log (α (n + j)) := rfl
    simp only [hA]
    rw [Real.log_div (hpos j).ne' hα0.ne', Real.log_div (hpos 1).ne' hα0.ne', ← hwj, hnew]
    simp only [hw, add_zero]
    ring
  have hγ := tendsto_gk_of_poly (D := D') hδ0 hδne hαpos (Qd α δ d) hdeg h0 hQ hφ
  have hEq : ∀ k, ∀ᶠ n in atTop, gk α (fun n => Real.exp (A n)) δ n k = gk α (fun n => α (n + 1) / α n) δ n k := by
    intro k
    obtain ⟨N, hN⟩ := eventually_atTop.mp hαpos
    filter_upwards [eventually_ge_atTop N] with n hn
    have h1 := hN n hn
    have h2 := hN (n + 1) (by omega)
    unfold gk wr
    simp only [hA]
    rw [Real.exp_log (div_pos h2 h1)]
  have hγ' : ∀ k ≤ d, Tendsto (fun n => gk α (fun n => α (n + 1) / α n) δ n k) atTop (𝓝 (GORZ.cH k)) :=
    fun k hk' => (hγ k hk').congr' (hEq k)
  have hEpos : ∀ᶠ n in atTop, 0 < α (n + 1) / α n := by
    obtain ⟨N, hN⟩ := eventually_atTop.mp hαpos
    filter_upwards [eventually_ge_atTop N] with n hn
    exact div_pos (hN (n + 1) (by omega)) (hN n hn)
  exact conclusions_of_gk hδ0 hδpos hEpos (hαpos.mono fun n h => h.ne') hγ'

/-! ## differences from derivatives -/

lemma sum_choose_real (K : ℕ) : ∑ j ∈ range (K + 1), (K.choose j : ℝ) = 2 ^ K := by
  exact_mod_cast Nat.sum_range_choose K

/-- **Differences from derivatives**: `|Δ^K[G 0](0) − G K (0)| ≤ 2^K K^{K+1} B` if `|G (K+1)| ≤ B` on `[0,K]`. -/
theorem fd_chain_close (G : ℕ → ℝ → ℝ) (K : ℕ)
    (hG : ∀ i < K + 1, ∀ t, 0 ≤ t → HasDerivAt (G i) (G (i + 1) t) t) {B : ℝ}
    (hB : ∀ t : ℝ, 0 ≤ t → t ≤ (K : ℝ) → |G (K + 1) t| ≤ B) :
    |GORZ.fd (fun j => G 0 j) K - G K 0| ≤ 2 ^ K * (K : ℝ) ^ (K + 1) * B := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 le_rfl (Nat.cast_nonneg K))
  set R : ℕ → ℝ := fun j => G 0 j - ∑ i ∈ range (K + 1), G i 0 * (j : ℝ) ^ i / (i.factorial : ℝ) with hR
  have hRb : ∀ j ≤ K, |R j| ≤ (K : ℝ) ^ (K + 1) * B := by
    intro j hj
    have hjK : (j : ℝ) ≤ K := by exact_mod_cast hj
    have ht := JensenThreshold.Tail.taylor_bounds G (K + 1) hG (X := K) (lo := -B) (hi := B)
      (fun t h1 h2 => by have := hB t h1 h2; constructor <;> linarith [abs_le.mp this])
      (Nat.cast_nonneg j) hjK
    have hf : (1 : ℝ) ≤ ((K + 1).factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hjp : (j : ℝ) ^ (K + 1) ≤ (K : ℝ) ^ (K + 1) := pow_le_pow_left₀ (Nat.cast_nonneg j) hjK _
    have hq : B * (j : ℝ) ^ (K + 1) / ((K + 1).factorial : ℝ) ≤ (K : ℝ) ^ (K + 1) * B := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_le_mul_of_nonneg_left hjp hB0, pow_nonneg (Nat.cast_nonneg (α := ℝ) K) (K + 1),
        mul_nonneg hB0 (pow_nonneg (Nat.cast_nonneg (α := ℝ) K) (K + 1))]
    rw [abs_le]
    constructor
    · have : -B * (j : ℝ) ^ (K + 1) / ((K + 1).factorial : ℝ) = -(B * (j : ℝ) ^ (K + 1) / ((K + 1).factorial : ℝ)) := by ring
      linarith [ht.1]
    · linarith [ht.2]
  have hsplit : GORZ.fd (fun j => G 0 j) K =
      ∑ i ∈ range (K + 1), G i 0 / (i.factorial : ℝ) * apow K i + GORZ.fd R K := by
    have hw : ∀ j : ℕ, G 0 j = (∑ i ∈ range (K + 1), G i 0 * (j : ℝ) ^ i / (i.factorial : ℝ)) + R j := by
      intro j; simp only [hR]; ring
    simp only [GORZ.fd, hw, mul_add, sum_add_distrib]
    congr 1
    simp only [apow, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  have hmain : ∑ i ∈ range (K + 1), G i 0 / (i.factorial : ℝ) * apow K i = G K 0 := by
    rw [Finset.sum_range_succ, Finset.sum_eq_zero fun i hi => by
      rw [apow_lt (Finset.mem_range.mp hi), mul_zero], zero_add, apow_self]
    field_simp
  rw [hsplit, hmain, add_sub_cancel_left]
  unfold GORZ.fd
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j ∈ range (K + 1), |(-1 : ℝ) ^ (K - j) * (K.choose j : ℝ) * R j|
      ≤ ∑ j ∈ range (K + 1), (K.choose j : ℝ) * ((K : ℝ) ^ (K + 1) * B) := by
        refine sum_le_sum fun j hj => ?_
        rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
        exact mul_le_mul_of_nonneg_left (hRb j (by simp at hj; omega)) (Nat.cast_nonneg _)
    _ = 2 ^ K * (K : ℝ) ^ (K + 1) * B := by rw [← Finset.sum_mul, sum_choose_real]; ring

end GORZXi
