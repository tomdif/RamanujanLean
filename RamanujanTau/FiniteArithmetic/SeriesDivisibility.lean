import RamanujanTau.FiniteArithmetic.AllPowers29

/-! Coefficientwise divisibility and cancellation of the common Euler factor. -/
set_option autoImplicit false
namespace RamanujanTau.FiniteArithmetic
open PowerSeries BoylanWebb AtkinOBrien AtkinOBrienFinal

lemma series_dvd_iff {p : ℕ} [Fact p.Prime] (m : ℕ) (F : PS p) :
    Dvd (p : ℤ_[p]) m F ↔ ∀ n, (p : ℤ_[p]) ^ m ∣ coeff n F := by
  constructor
  · rintro ⟨G, hG⟩ n
    refine ⟨coeff n G, ?_⟩
    rw [hG, coeff_smul, smul_eq_mul]
  · intro h
    choose G hG using h
    refine ⟨PowerSeries.mk G, ?_⟩
    ext n
    rw [coeff_smul, coeff_mk, smul_eq_mul, hG]

lemma partition_series_dvd_iff {p : ℕ} [Fact p.Prime]
    (h24 : 24 * δ p + 1 = p ^ 2) (m b : ℕ) (c : ℤ_[p]) :
    Dvd (p : ℤ_[p]) m (Ll p (b + 2) - c • Ll p b) ↔
      ∀ t : ℕ, (p : ℤ_[p]) ^ m ∣
        (pZ ((p : ℤ) ^ (b + 2) * t - eB p (b + 2)) : ℤ_[p]) -
          c * (pZ ((p : ℤ) ^ b * t - eB p b) : ℤ_[p]) := by
  constructor
  · exact fun h t => AllPowers29.pser_dvd_precision h24 c b m h t
  · intro h
    have hd : Dvd (p : ℤ_[p]) m
        (PowerSeries.map (Int.castRingHom ℤ_[p]) (Pser p (b + 2)) -
          c • PowerSeries.map (Int.castRingHom ℤ_[p]) (Pser p b)) := by
      apply (series_dvd_iff m _).mpr
      intro t
      simpa only [map_sub, coeff_smul, coeff_map, Pser, coeff_mk, smul_eq_mul,
        Int.coe_castRingHom] using h t
    obtain ⟨Q, _, h1, h2⟩ := L_factor h24 b
    obtain ⟨G, hG⟩ := hd
    refine ⟨PowerSeries.map (Int.castRingHom ℤ_[p]) Q * G, ?_⟩
    change PowerSeries.map (Int.castRingHom ℤ_[p]) (L p (b + 2)) -
      c • PowerSeries.map (Int.castRingHom ℤ_[p]) (L p b) = _
    rw [h1, h2, map_mul, map_mul, ← mul_smul_comm, ← mul_sub, hG, mul_smul_comm]

end RamanujanTau.FiniteArithmetic
