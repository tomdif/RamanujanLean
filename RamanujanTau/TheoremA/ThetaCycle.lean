import Mathlib.Tactic

/-!
# The numerical theta-cycle obstruction at weight `p - 3`

This file proves the integer bookkeeping needed by the proposed Theorem A.
It does not assert that modular-form filtrations satisfy the hypotheses.
That level-six geometric input remains a separate formalization obligation.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA

private lemma not_dvd_between {p r : ℤ} (hr : 0 < r) (hrp : r < p) : ¬ p ∣ r := by
  intro h
  have := Int.le_of_dvd hr h
  omega

/-- The weight `p - 3` case of Lemma T. A nonnegative closed filtration cycle,
whose drops occur only at multiples of `p`, has weight six after four steps.
No primality hypothesis is needed for this numerical implication. -/
theorem theta_cycle_weight_six (p : ℕ) (hp : 13 ≤ p) (w d : ℕ → ℤ)
    (hw : ∀ i ≤ p - 1, 0 ≤ w i)
    (hd : ∀ i < p - 1, 0 ≤ d i)
    (hstep : ∀ i < p - 1,
      w (i + 1) = w i + p + 1 - d i * (p - 1 : ℤ))
    (hdrop : ∀ i < p - 1, ¬ (p : ℤ) ∣ w i → d i = 0)
    (hstart : w 0 = (p : ℤ) - 3) (hclose : w (p - 1) = w 0) : w 4 = 6 := by
  have hpz : (13 : ℤ) ≤ p := by exact_mod_cast hp
  have h0 : d 0 = 0 := hdrop 0 (by omega) (by
    rw [hstart]
    exact not_dvd_between (by omega) (by omega))
  have h1 : w 1 = 2 * (p : ℤ) - 2 := by
    have := hstep 0 (by omega)
    simp only [h0, zero_mul, sub_zero, hstart] at this
    linarith
  have hd1 : d 1 = 0 := hdrop 1 (by omega) (by
    rw [h1]
    intro h
    have htwo : (p : ℤ) ∣ 2 := by
      have := dvd_sub (dvd_mul_left (p : ℤ) 2) h
      convert this using 1; ring
    exact not_dvd_between (by norm_num) (by omega) htwo)
  have h2 : w 2 = 3 * (p : ℤ) - 1 := by
    have := hstep 1 (by omega)
    simp only [hd1, zero_mul, sub_zero, h1] at this
    linarith
  have hd2 : d 2 = 0 := hdrop 2 (by omega) (by
    rw [h2]
    intro h
    have hone : (p : ℤ) ∣ 1 := by
      have := dvd_sub (dvd_mul_left (p : ℤ) 3) h
      convert this using 1; ring
    exact not_dvd_between (by norm_num) (by omega) hone)
  have h3 : w 3 = 4 * (p : ℤ) := by
    have := hstep 2 (by omega)
    simp only [hd2, zero_mul, sub_zero, h2] at this
    linarith
  have h4 : w 4 = 5 * (p : ℤ) + 1 - d 3 * (p - 1 : ℤ) := by
    have := hstep 3 (by omega)
    rw [h3] at this
    linarith
  have ds0 : 0 ≤ d 3 := hd 3 (by omega)
  have ds5 : d 3 ≤ 5 := by
    have := hw 4 (by omega)
    rw [h4] at this
    by_contra hn
    have : 6 ≤ d 3 := by omega
    nlinarith
  have ds : d 3 = 5 := by
    by_contra hn
    have ds4 : d 3 ≤ 4 := by omega
    have run : ∀ n ≤ p - 5, w (4 + n) = w 4 + n * ((p : ℤ) + 1) := by
      intro n hn
      induction n with
      | zero => simp
      | succ n ih =>
        have hn' : n ≤ p - 5 := by omega
        have hi : 4 + n < p - 1 := by omega
        have hdn : d (4 + n) = 0 := hdrop _ hi (by
          rw [ih hn', h4]
          intro h
          have hrem : (p : ℤ) ∣ d 3 + 1 + n := by
            have hmultiple : (p : ℤ) ∣ (5 - d 3 + n) * p := dvd_mul_left _ _
            have := dvd_sub h hmultiple
            convert this using 1; ring
          exact not_dvd_between (by positivity) (by omega) hrem)
        have hs := hstep (4 + n) hi
        rw [hdn, zero_mul, sub_zero, ih hn'] at hs
        push_cast
        convert hs using 1; ring
    have hend := run (p - 5) (by omega)
    have heq : 4 + (p - 5) = p - 1 := by omega
    rw [heq, hclose, hstart, h4] at hend
    have hc : ((p - 5 : ℕ) : ℤ) = (p : ℤ) - 5 := by omega
    rw [hc] at hend
    nlinarith
  rw [h4, ds]
  ring

end RamanujanTau.TheoremA
