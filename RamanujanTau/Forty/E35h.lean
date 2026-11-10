/-
# Entry 3.35 with the square root

`entry_3_35` (`E35g.lean`) is the squared form. Here the branch is fixed: `AB − x − 2q² − 2q⁴/x` is divisible by `q`,
the quotient `r` satisfies `r² = 4x + 9q² + 8q⁴/x`, and `r(0) = 2` (computed modulo `q²`: `χ(q) ≡ 1 + q`,
`χ(−q) ≡ 1 − q`, `χ(±q⁴⁷) ≡ 1`). So
`AB = x + 2q² + 2q⁴/x + q√(4x + 9q² + 8q⁴/x)` with the principal root (`entry_3_35_root`), and that root is the only
series with constant term `2` and the right square (`entry_3_35_unique`).
-/
import RamanujanTau.Forty.E35g

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC PowerSeries
open RankProof (Pinf isUnit_Pinf)

/-- the ideal `(q²)`. -/
noncomputable abbrev I2 : Ideal (PowerSeries ℤ) := Ideal.span {(X : PowerSeries ℤ) ^ 2}

local notation "π2" => Ideal.Quotient.mk I2

lemma π2_eq {f g : PowerSeries ℤ} (h : (X : PowerSeries ℤ) ^ 2 ∣ f - g) : π2 f = π2 g :=
  Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr h)

lemma π2_zero {f : PowerSeries ℤ} (h : π2 f = 0) : (X : PowerSeries ℤ) ^ 2 ∣ f :=
  Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h)

lemma hx2 : (π2 X) ^ 2 = 0 := by
  rw [← map_pow]; exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr dvd_rfl)

lemma hx2n (n : ℕ) (hn : 2 ≤ n) : (π2 X) ^ n = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [_root_.pow_add, hx2, zero_mul]

lemma π2Pinf (b a : ℕ) (hb : 1 ≤ b) (ha : 1 ≤ a) : π2 (Pinf b a) = 1 - π2 X ^ b := by
  rw [π2_eq (RankProof.X_pow_dvd_Pinf_sub b a hb ha 1)]
  simp [RankProof.Pfin]

lemma π2S (a : ℕ) [NeZero a] (ha : 2 ≤ a) (f : PowerSeries ℤ) (hf : constantCoeff f = 1) : π2 (S a f) = 1 := by
  rw [← map_one π2]
  apply π2_eq
  have h1 : (X : PowerSeries ℤ) ^ 1 ∣ f - 1 := by
    rw [pow_one, X_dvd_iff]; simp [hf]
  have h2 := RankProof.Ea_dvd a (NeZero.ne a) h1
  have h3 : S a f - 1 = S a (f - 1) := by rw [map_sub, map_one]
  rw [h3]
  exact (pow_dvd_pow X (by omega)).trans h2

lemma cc_u47 : constantCoeff u47 = 1 := by
  rw [u47, map_mul, cc_chip, cc_chip, mul_one]

lemma cc_v47 : constantCoeff v47 = 1 := by
  simp only [v47, chim, map_mul]
  rw [cc_Pinf 1 (2 * 1) le_rfl (by norm_num), cc_Pinf 47 (2 * 47) (by norm_num) (by norm_num), mul_one]

lemma π2_u47 : π2 u47 = 1 + π2 X := by
  have hc := congrArg π2 (chip_mul 1)
  simp only [map_mul, Nat.reduceMul, π2Pinf 1 2 le_rfl (by norm_num), π2Pinf 2 4 (by norm_num) (by norm_num)] at hc
  have h47 : π2 (chip 47) = 1 := by
    rw [chip]
    exact π2S 47 (by norm_num) _ (by rw [cc_Ng, cc_Pinf 1 2 le_rfl (by norm_num)])
  rw [u47, map_mul, h47, mul_one]
  linear_combination (1 + π2 X) * hc + (π2 (chip 1) - 1 - π2 X) * hx2

lemma π2_v47 : π2 v47 = 1 - π2 X := by
  simp only [v47, chim, Nat.reduceMul, map_mul, π2Pinf 1 2 le_rfl (by norm_num),
    π2Pinf 47 94 (by norm_num) (by norm_num), hx2n 47 (by norm_num)]
  ring

/-- **Entry 3.35** with the square root: `AB = x + 2q² + 2q⁴/x + q r`, `r² = 4x + 9q² + 8q⁴/x`, `r(0) = 2`
(`x = χ(−q)χ(−q⁴⁷)`, `AB` the product of the two Rogers–Ramanujan brackets). -/
theorem entry_3_35_root : ∃ r : PowerSeries ℤ,
    r ^ 2 = 4 * (chim 1 * chim 47) + 9 * X ^ 2 + 8 * X ^ 4 * Ring.inverse (chim 1 * chim 47) ∧
    constantCoeff r = 2 ∧
    (G * S 94 G + X ^ 19 * H * S 94 H) * (S 47 G * S 2 H - X ^ 9 * S 2 G * S 47 H) =
      chim 1 * chim 47 + 2 * X ^ 2 + 2 * X ^ 4 * Ring.inverse (chim 1 * chim 47) + X * r := by
  have hsq := entry_3_35
  have hAB := entry_3_35_AB
  rw [chim_w47] at hAB
  rw [show chim 1 * chim 47 = v47 from rfl] at hsq ⊢
  set AB := (G * S 94 G + X ^ 19 * H * S 94 H) * (S 47 G * S 2 H - X ^ 9 * S 2 G * S 47 H) with hABdef
  set D := AB - v47 - 2 * X ^ 2 - 2 * X ^ 4 * Ring.inverse v47 with hD
  have hu : chip 1 * chip 47 = u47 := rfl
  rw [hu] at hAB
  have hDY : D = (u47 - v47) + X ^ 2 * (1 + 2 * X ^ 4 * Ring.inverse (u47 * v47)
      + 2 * X ^ 2 * u47 * Ring.inverse (u47 * v47) - 2 - 2 * X ^ 2 * Ring.inverse v47) := by
    rw [hD, hAB]; ring
  have hcc : constantCoeff D = 0 := by
    rw [hDY]
    simp only [map_add, map_sub, map_mul, map_pow, constantCoeff_X, cc_u47, cc_v47]
    ring
  obtain ⟨r, hr⟩ := X_dvd_iff.mpr hcc
  have hr2 : r ^ 2 = 4 * v47 + 9 * X ^ 2 + 8 * X ^ 4 * Ring.inverse v47 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 (X_ne_zero : (X : PowerSeries ℤ) ≠ 0))
    rw [← hsq, hr]
    ring
  set c := constantCoeff r with hcdef
  have hc : c = 2 := by
    obtain ⟨r', hr'⟩ := X_dvd_iff.mpr (show constantCoeff (r - (c : PowerSeries ℤ)) = 0 by
      simp [hcdef])
    have e1 : π2 D = (1 + π2 X) - (1 - π2 X) + π2 X ^ 2 * π2 (1 + 2 * X ^ 4 * Ring.inverse (u47 * v47)
        + 2 * X ^ 2 * u47 * Ring.inverse (u47 * v47) - 2 - 2 * X ^ 2 * Ring.inverse v47) := by
      rw [hDY, map_add, map_sub, map_mul, map_pow, π2_u47, π2_v47]
    have e2 := congrArg π2 hr
    rw [show r = (c : PowerSeries ℤ) + X * r' by linear_combination hr'] at e2
    simp only [map_add, map_mul] at e2
    have h0 : π2 (X * ((c : PowerSeries ℤ) - 2)) = 0 := by
      simp only [map_mul, map_sub, map_ofNat]
      linear_combination -(e1.symm.trans e2)
        + (π2 (1 + 2 * X ^ 4 * Ring.inverse (u47 * v47) + 2 * X ^ 2 * u47 * Ring.inverse (u47 * v47) - 2
          - 2 * X ^ 2 * Ring.inverse v47) - π2 r') * hx2
    have h1 := π2_zero h0
    rw [sq] at h1
    have h2 := (mul_dvd_mul_iff_left (X_ne_zero : (X : PowerSeries ℤ) ≠ 0)).mp h1
    have h3 := X_dvd_iff.mp h2
    simp only [map_sub, map_intCast, map_ofNat] at h3
    exact_mod_cast sub_eq_zero.mp h3
  refine ⟨r, hr2, hc, ?_⟩
  linear_combination hr - hD - hABdef

/-- the root in `entry_3_35_root` is unique: any series `r` with `r² = 4x + 9q² + 8q⁴/x` and `r(0) = 2` gives
`AB = x + 2q² + 2q⁴/x + q r`. -/
theorem entry_3_35_unique (r : PowerSeries ℤ)
    (hr : r ^ 2 = 4 * (chim 1 * chim 47) + 9 * X ^ 2 + 8 * X ^ 4 * Ring.inverse (chim 1 * chim 47))
    (hc : constantCoeff r = 2) :
    (G * S 94 G + X ^ 19 * H * S 94 H) * (S 47 G * S 2 H - X ^ 9 * S 2 G * S 47 H) =
      chim 1 * chim 47 + 2 * X ^ 2 + 2 * X ^ 4 * Ring.inverse (chim 1 * chim 47) + X * r := by
  obtain ⟨r0, h0, hc0, hAB⟩ := entry_3_35_root
  have hf : (r - r0) * (r + r0) = 0 := by linear_combination hr - h0
  rcases mul_eq_zero.mp hf with h | h
  · rw [hAB, sub_eq_zero.mp h]
  · exfalso
    have := congrArg constantCoeff h
    rw [map_add, hc, hc0, map_zero] at this
    norm_num at this

end Forty
