import RamanujanTau.ThetaLift.GeneralLift

/-!
# The lift of a `U`-kernel

If the coordinate `A[m] = a(24m - j)` vanishes modulo `ℓ` whenever `ℓ ∣ 24m - j`, then the coefficients of the lift at multiples of `ℓ`
vanish modulo `ℓ`. So the lift of an element of `ker U` lies in `ker U` in weight `2λ`.
-/

set_option autoImplicit false

namespace RamanujanTau.ThetaLift
open RamanujanTau.TheoremA.HalfIntegral RamanujanTau.TheoremA.SignLattice

/-- **The lift carries `ker U` to `ker U`.** -/
theorem genLift_U_dvd {ℓ j lam t : ℕ} (hp : ℓ.Prime) (hlam : 2 ≤ lam) (ht : 24 ∣ t + j) {A : PowerSeries ℤ}
    (hA : ∀ m : ℕ, (ℓ : ℤ) ∣ (24 * (m : ℤ) - j) → (ℓ : ℤ) ∣ A.coeff m) (n : ℕ) :
    (ℓ : ℤ) ∣ (genLift j lam t A).coeff (ℓ * n) := by
  rw [genLift, PowerSeries.coeff_mk]
  refine Finset.dvd_sum ?_
  rintro ⟨d, e⟩ hx
  have hm := (Nat.mem_divisorsAntidiagonal.mp hx).1
  simp only at hm ⊢
  have hprod : ℓ ∣ d * e := hm ▸ dvd_mul_right ℓ n
  rcases (Nat.Prime.dvd_mul hp).mp hprod with hd | he
  · refine dvd_mul_of_dvd_left ?_ _
    unfold psi
    refine dvd_mul_of_dvd_right ?_ _
    obtain ⟨c, rfl⟩ := hd
    obtain ⟨u, hu⟩ : ∃ u, lam - 1 = u + 1 := ⟨lam - 2, by omega⟩
    rw [hu, pow_succ]
    push_cast
    exact Dvd.dvd.mul_left (dvd_mul_right _ _) _
  · by_cases h6 : e % 2 = 0 ∨ e % 3 = 0
    · have h0 : chi12 e = 0 := by
        unfold chi12
        have : e % 12 = 0 ∨ e % 12 = 2 ∨ e % 12 = 3 ∨ e % 12 = 4 ∨ e % 12 = 6 ∨ e % 12 = 8 ∨ e % 12 = 9 ∨ e % 12 = 10 := by
          omega
        rcases this with h | h | h | h | h | h | h | h <;> simp [h]
      simp [h0]
    · have he2 : ¬ 2 ∣ e := by omega
      have he3 : ¬ 3 ∣ e := by omega
      have hsq := sq_mod_24 he2 he3
      obtain ⟨u, hu⟩ := ht
      obtain ⟨v, hv⟩ : ∃ v, e ^ 2 = 24 * v + 1 := ⟨e ^ 2 / 24, by omega⟩
      have h24 : t * e ^ 2 + j = 24 * (t * v + u) := by
        rw [hv]
        linarith [hu, mul_add t (24 * v) 1]
      have hidx : (t * e ^ 2 + j) / 24 = t * v + u := by
        rw [h24, Nat.mul_div_cancel_left _ (by norm_num)]
      refine dvd_mul_of_dvd_right (dvd_mul_of_dvd_right ?_ _) _
      rw [hidx]
      apply hA
      have e1 : 24 * (((t * v + u : ℕ) : ℤ)) - j = t * (e : ℤ) ^ 2 := by
        have h' : ((t * e ^ 2 + j : ℕ) : ℤ) = 24 * ((t * v + u : ℕ) : ℤ) := by exact_mod_cast h24
        push_cast at h' ⊢
        linarith
      rw [e1]
      obtain ⟨c, rfl⟩ := he
      push_cast
      exact ⟨t * ((ℓ : ℤ) * c ^ 2), by ring⟩

end RamanujanTau.ThetaLift
