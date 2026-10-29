import RamanujanTau.FiniteArithmetic.ModularCertificate

/-! Finite inverse certificates, valid at composite as well as prime moduli. -/
set_option autoImplicit false
namespace BoylanWebb
open PowerSeries RamanujanTau

theorem Cg_inverse {p d : ℕ} {F G : PowerSeries ℤ} (hFG : F * G = 1)
    {a b : List ℤ} (hF : Cg p d F (toPS a))
    (hcheck : Cg p d (toPS (tmul p d a b)) 1) : Cg p d G (toPS b) := by
  have h := (Cg_tmul hF (Cg.refl (toPS b))).trans hcheck
  have hmul : Ψ p F * Ψ p G = 1 := by rw [← map_mul, hFG, map_one]
  have he : Ψ p G - Ψ p (toPS b) = -(Ψ p G * (Ψ p (F * toPS b) - Ψ p 1)) := by
    rw [map_mul, map_one]
    linear_combination (Ψ p (toPS b)) * hmul
  unfold Cg at h ⊢
  rw [he]
  exact dvd_neg.mpr (Dvd.dvd.mul_left h _)

theorem Cg_expand {p d : ℕ} {F G : PowerSeries ℤ} (k : ℕ) (hk : k ≠ 0)
    (h : Cg p d F G) : Cg p d (RankProof.Ea k hk F) (RankProof.Ea k hk G) := by
  rw [Cg, PowerSeries.X_pow_dvd_iff] at h ⊢
  intro n hn
  simp only [map_sub, coeff_map, RankProof.coeff_Ea]
  split_ifs with hd
  · have hh := h (n / k) (by have := Nat.div_le_self n k; omega)
    simpa only [map_sub, coeff_map] using hh
  · simp

end BoylanWebb
