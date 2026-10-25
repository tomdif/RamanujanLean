import RamanujanTau.MTC.UDecL
set_option autoImplicit false
namespace MTC
open ALz HahnSeries Finset

/-- **uniform decay of the `Λ`-family**, with `|ℓ(k)| ≤ 2|k| + B₀`. -/
theorem udec_lam2 {N : ℕ} (hN : 1 ≤ N) {d : ℤ} (hd : d ≠ 0) (eb : ℤ → ℤ) (Eb : ℤ) (hEb : ∀ k, |eb k| ≤ Eb)
    (cb : ℂ) (ℓ : ℤ → ℤ) (B0 : ℤ)
    (hℓ : ∀ k, |ℓ k| ≤ 2 * |k| + B0) (σ : ℤ → L) {M : ℤ} (hM : 1 ≤ M) (C0 : ℤ)
    (hσ : ∀ k, vge (σ k) (M * c2 k - C0)) :
    UDec (fun k n => σ k * lamX hN (ℓ k) d (eb k) cb n) := by
  intro A
  have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
  obtain ⟨Ck, hCk⟩ := quad_dom hM (2 * N + 1)
  obtain ⟨Cj, hCj⟩ := quad_dom hN' (|A| * |d| + N + Eb)
  refine ⟨Ck + Cj + N * B0 + N + C0, fun k n => ?_⟩
  unfold lamX
  simp only [shiftS, subst]
  split_ifs with hdv
  · obtain ⟨m, hm⟩ := hdv
    have hj : d ∣ n := ⟨m - (ℓ k - 1), by linear_combination hm⟩
    obtain ⟨j, rfl⟩ := hj
    have hmj : m = j + ℓ k - 1 := by
      have : d * m = d * (j + ℓ k - 1) := by linear_combination -hm
      exact mul_left_cancel₀ hd this
    rw [hm, Int.mul_ediv_cancel_left _ hd, hmj]
    refine vge_mono (vge_mul (hσ k) (vge_mul (vge_single _ _) (vge_mul (vge_lam0S hN _) (vge_single _ _)))) ?_
    have e1 := c2_add j (ℓ k)
    have hjl : |j + ℓ k - 1| ≤ |j| + |ℓ k| + 1 := by
      have := le_abs_self j; have := neg_abs_le j; have := le_abs_self (ℓ k); have := neg_abs_le (ℓ k)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hA : A * |d * j| ≤ |A| * |d| * |j| := by
      rw [abs_mul, ← mul_assoc]; exact (le_abs_self _).trans (by rw [abs_mul, abs_mul, abs_abs, abs_abs])
    have hebj : -(Eb * |j|) ≤ eb k * j := by
      have h1 : -(|eb k| * |j|) ≤ eb k * j := by rw [← abs_mul]; exact neg_abs_le _
      have h2 : |eb k| * |j| ≤ Eb * |j| := mul_le_mul_of_nonneg_right (hEb k) (abs_nonneg j)
      linarith
    have h1 := hCk k; have h2 := hCj j; have h3 := hℓ k
    have hNl : (N : ℤ) * |ℓ k| ≤ N * (2 * |k| + B0) := mul_le_mul_of_nonneg_left h3 (by positivity)
    have hNjl : (N : ℤ) * |j + ℓ k - 1| ≤ N * (|j| + |ℓ k| + 1) := mul_le_mul_of_nonneg_left hjl (by positivity)
    rw [show j + ℓ k - 1 + 1 = j + ℓ k by ring, e1]
    nlinarith [abs_nonneg j, abs_nonneg k, abs_nonneg A, abs_nonneg d]
  · simp only [mul_zero]
    exact vge_zero _

end MTC
