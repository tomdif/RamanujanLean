/-
# Log-concavity of the partition function (DeSalvo–Pak 2015)

**`partition_logConcave`**: `p(n−1)·p(n+1) < p(n)²` for every `n ≥ 26`.

* For `26 ≤ n ≤ 548`: kernel computation from a certified table of `p(n)` (`LogConcaveTable`).
* For `n ≥ 549`: `U = u₁(n) ≥ 60`. Rademacher's series gives `|p(m) − K e^{u}f(u)| ≤ K e^{u}g(u)`
  (`p_sub_main_le`, with `f(u) = (u−1)/(2u³)` and `g(u) = e^{−u/2}`). The main-term inequality
  (`main_ineq`) then compares `n − 1, n, n + 1` through `u_{n±1}² = U² ± 2π²/3`.

The bound `26` is sharp: the inequality fails exactly at the odd `n ≤ 25` (`logConcave_fails`), e.g.
`p(24)p(26) = 1575·2436 ≥ 1958² = p(25)²`.
-/
import RamanujanTau.LogConcaveTable
import RamanujanTau.LogConcaveIneq
import RamanujanTau.Rademacher.LogConcaveTail

set_option autoImplicit false

namespace LogConcave
open Real Rademacher

noncomputable section

lemma uk_sq {m : ℕ} (hm : 1 ≤ m) : uk 1 m ^ 2 = π ^ 2 * ((2 / 3) * ((m : ℝ) - 1 / 24)) := by
  have : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [uk, Nat.cast_one, div_one, mul_pow, Real.sq_sqrt (by nlinarith)]

lemma Mmain_eq (n : ℕ) : Mmain n = Kc * exp (uk 1 n) * ff (uk 1 n) := by
  unfold Mmain ff; ring

lemma err_eq (n : ℕ) : Kc * exp (uk 1 n / 2) = Kc * exp (uk 1 n) * gg (uk 1 n) := by
  unfold gg
  rw [mul_assoc, ← Real.exp_add]; congr 2; ring

set_option maxHeartbeats 1600000 in
theorem logConcave_large {n : ℕ} (hn : 549 ≤ n) :
    (HardyRamanujan.p (n - 1) : ℝ) * HardyRamanujan.p (n + 1) < (HardyRamanujan.p n : ℝ) ^ 2 := by
  have hpi1 := pi_gt_d2
  have hpi2 := pi_lt_d2
  set U := uk 1 n
  set up := uk 1 (n + 1)
  set um := uk 1 (n - 1)
  have hnr : (549 : ℝ) ≤ n := by exact_mod_cast hn
  have hU2 := uk_sq (m := n) (by omega)
  have hup2 := uk_sq (m := n + 1) (by omega)
  have hum2 := uk_sq (m := n - 1) (by omega)
  push_cast [Nat.cast_sub (by omega : 1 ≤ n)] at hup2 hum2
  set γ := 2 / 3 * π ^ 2 with hγ
  have hU0 : 0 < U := uk_pos one_pos (by omega)
  have hup : 0 < up := uk_pos one_pos (by omega)
  have hum : 0 < um := uk_pos one_pos (by omega)
  have hU60 : 60 ≤ U := by
    have : 3600 ≤ U ^ 2 := by rw [hU2]; nlinarith
    nlinarith
  have hγ1 : 6.5 ≤ γ := by rw [hγ]; nlinarith
  have hγ2 : γ ≤ 6.7 := by rw [hγ]; nlinarith
  have e1 : up ^ 2 = U ^ 2 + γ := by rw [hup2, hU2, hγ]; ring
  have e2 : um ^ 2 = U ^ 2 - γ := by rw [hum2, hU2, hγ]; ring
  obtain ⟨hmain, hpos⟩ := main_ineq hU60 hγ1 hγ2 hup hum e1 e2
  have hK := Kc_pos
  -- the three error bounds
  have b0 := p_sub_main_le n (by omega)
  have bp := p_sub_main_le (n + 1) (by omega)
  have bm := p_sub_main_le (n - 1) (by omega)
  rw [Mmain_eq, err_eq] at b0 bp bm
  rw [abs_le] at b0 bp bm
  have lo0 : Kc * exp U * (ff U - gg U) ≤ (HardyRamanujan.p n : ℝ) := by
    have := b0.1; nlinarith
  have hip : (HardyRamanujan.p (n + 1) : ℝ) ≤ Kc * exp up * (ff up + gg up) := by
    have := bp.2; nlinarith
  have him : (HardyRamanujan.p (n - 1) : ℝ) ≤ Kc * exp um * (ff um + gg um) := by
    have := bm.2; nlinarith
  have hp0 : (0 : ℝ) ≤ HardyRamanujan.p (n + 1) := by positivity
  have hm0 : (0 : ℝ) ≤ HardyRamanujan.p (n - 1) := by positivity
  have hfgp : 0 ≤ ff up + gg up :=
    add_nonneg (ff_nonneg (by nlinarith)) (exp_pos _).le
  have hlo0 : 0 ≤ Kc * exp U * (ff U - gg U) := by
    have := exp_pos U
    have : 0 ≤ ff U - gg U := by linarith
    positivity
  calc (HardyRamanujan.p (n - 1) : ℝ) * HardyRamanujan.p (n + 1)
      ≤ (Kc * exp um * (ff um + gg um)) * (Kc * exp up * (ff up + gg up)) :=
        mul_le_mul him hip hp0 (le_trans hm0 him)
    _ = Kc ^ 2 * exp (2 * U) * (exp (up + um - 2 * U) * (ff up + gg up) * (ff um + gg um)) := by
        have hE : exp um * exp up = exp (2 * U) * exp (up + um - 2 * U) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
        calc Kc * exp um * (ff um + gg um) * (Kc * exp up * (ff up + gg up))
            = Kc ^ 2 * (exp um * exp up) * ((ff up + gg up) * (ff um + gg um)) := by ring
          _ = _ := by rw [hE]; ring
    _ < Kc ^ 2 * exp (2 * U) * (ff U - gg U) ^ 2 :=
        mul_lt_mul_of_pos_left hmain (by positivity)
    _ = (Kc * exp U * (ff U - gg U)) ^ 2 := by
        rw [show exp (2 * U) = exp U ^ 2 by rw [← Real.exp_nat_mul]; norm_num]; ring
    _ ≤ (HardyRamanujan.p n : ℝ) ^ 2 := pow_le_pow_left₀ hlo0 lo0 2

/-- **DeSalvo–Pak**: `p(n)` is log-concave for `n ≥ 26`: `p(n−1)·p(n+1) < p(n)²`. -/
theorem partition_logConcave {n : ℕ} (hn : 26 ≤ n) :
    HardyRamanujan.p (n - 1) * HardyRamanujan.p (n + 1) < HardyRamanujan.p n ^ 2 := by
  rcases le_or_gt n 548 with h | h
  · have := logConcave_table hn h
    exact_mod_cast this
  · have := logConcave_large (n := n) (by omega)
    exact_mod_cast this

/-- the failures: `p(n)² ≤ p(n−1)p(n+1)` for every odd `n ≤ 25`. -/
theorem logConcave_fails : ∀ n ∈ [1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25],
    (Fintype.card (Nat.Partition n) : ℤ) ^ 2 ≤
      Fintype.card (Nat.Partition (n - 1)) * Fintype.card (Nat.Partition (n + 1)) := by
  intro n hn
  have hle : n ≤ 25 := by simp at hn; omega
  rw [← getP_eq (N := 27) (by omega), ← getP_eq (N := 27) (by omega), ← getP_eq (N := 27) (by omega)]
  revert n
  decide +kernel

end

end LogConcave
