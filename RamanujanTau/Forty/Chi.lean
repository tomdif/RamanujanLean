/-
# `χ(q) = (−q;q²)_∞` as a product quotient

`chip_mul`: `χ(q^a) (q^a;q^{2a})_∞ = (q^{2a};q^{4a})_∞`, i.e. `χ(q) = (q²;q⁴)_∞/(q;q²)_∞` (Euler).
-/
import RamanujanTau.Forty.Defs

set_option autoImplicit false

namespace Forty
open PowerSeries Finset
open RankProof (Pinf Pfin Pinf_ext X_pow_dvd_Pinf_sub isUnit_Pinf)

lemma Ng_X_pow_dvd {n : ℕ} {f : PowerSeries ℤ} (h : (X : PowerSeries ℤ) ^ n ∣ f) : (X : PowerSeries ℤ) ^ n ∣ Ng f := by
  obtain ⟨d, rfl⟩ := h
  refine ⟨(-1) ^ n * Ng d, ?_⟩
  rw [map_mul, map_pow, Ng, rescale_X, map_neg, map_one, neg_one_mul, neg_pow X n]
  ring

lemma Ng_Pfin_mul (M : ℕ) : Ng (Pfin 1 2 M) * Pfin 1 2 M = Pfin 2 4 M := by
  simp only [Pfin, map_prod, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  have hodd : Odd (1 + 2 * i) := ⟨i, by ring⟩
  rw [map_sub, map_one, map_pow, Ng, rescale_X, mul_pow, ← map_pow, hodd.neg_one_pow]
  simp only [map_neg, map_one, neg_one_mul]
  rw [show 2 + 4 * i = 2 * (1 + 2 * i) by ring, pow_mul]
  ring

/-- `(−q;q²)_∞ (q;q²)_∞ = (q²;q⁴)_∞`. -/
theorem Ng_Pinf_mul : Ng (Pinf 1 2) * Pinf 1 2 = Pinf 2 4 := by
  refine Pinf_ext (by norm_num) (by norm_num) fun N => ?_
  have h1 := X_pow_dvd_Pinf_sub 1 2 le_rfl (by norm_num) N
  rw [← Ng_Pfin_mul N,
    show Ng (Pinf 1 2) * Pinf 1 2 - Ng (Pfin 1 2 N) * Pfin 1 2 N
      = Ng (Pinf 1 2) * (Pinf 1 2 - Pfin 1 2 N) + Ng (Pinf 1 2 - Pfin 1 2 N) * Pfin 1 2 N by
        rw [map_sub]; ring]
  exact dvd_add (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_left (Ng_X_pow_dvd h1) _)

/-- `χ(q^a) (q^a;q^{2a})_∞ = (q^{2a};q^{4a})_∞`. -/
theorem chip_mul (a : ℕ) [NeZero a] : chip a * Pinf a (2 * a) = Pinf (2 * a) (4 * a) := by
  have h := congrArg (S a) Ng_Pinf_mul
  rw [map_mul, S_Pinf a 1 2 le_rfl (by norm_num), S_Pinf a 2 4 (by norm_num) (by norm_num)] at h
  rw [chip, mul_one, mul_comm a 2, mul_comm a 4] at *
  exact h

lemma chip_eq (a : ℕ) [NeZero a] : chip a = Pinf (2 * a) (4 * a) * Ring.inverse (Pinf a (2 * a)) := by
  have hu := isUnit_Pinf a (2 * a) (Nat.one_le_iff_ne_zero.mpr (NeZero.ne a)) (by have := NeZero.ne a; omega)
  rw [← chip_mul, mul_assoc, Ring.mul_inverse_cancel _ hu, mul_one]

end Forty
