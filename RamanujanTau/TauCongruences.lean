/-
# Elementary congruences for Ramanujan's `τ`

With `τ(n) = [qⁿ] q ∏_{k≥1} (1 − qᵏ)²⁴`:

* **`τ(n)` is odd iff `n` is an odd square** (`tau_odd_iff`).
* **`τ(n) ≡ 0 (mod 7)` whenever `n ≡ 0, 3, 5, 6 (mod 7)`** (`tau_mod7`), i.e. when `n` is `0` or a quadratic
  non-residue mod 7.

Both come from Frobenius and Jacobi's cube identity `(q;q)_∞³ = Σ (−1)ᵐ(2m+1) q^{m(m+1)/2}`:
`q(q;q)²⁴ ≡ q (q⁸;q⁸)³ (mod 2)` and `q(q;q)²⁴ ≡ q (q⁷;q⁷)³ (q;q)³ (mod 7)`. Since `8·(1 + m(m+1)/2) = (2m+1)² + 7`,
the exponent `1 + m(m+1)/2` lies in the class of `(2m+1)²` mod 7.
-/
import RamanujanTau.RankTheta
import RamanujanTau.MockTheta5Qfac4

set_option autoImplicit false

namespace TauCong
open PowerSeries Finset MockTheta5.Bailey MockTheta5.JTP
open RankProof (Ea Ea_X coeff_Ea)

/-- Ramanujan's `τ(n) = [qⁿ] q ∏ (1 − qᵏ)²⁴`. -/
noncomputable def tauPS (n : ℕ) : ℤ := coeff n (X * qfacInf ^ 24)

/-! ## Frobenius -/

section Frob
variable (p : ℕ) [hp : Fact p.Prime]

noncomputable def Ψ : PowerSeries ℤ →+* PowerSeries (ZMod p) := PowerSeries.map (Int.castRingHom (ZMod p))

instance charP_ps : CharP (PowerSeries (ZMod p)) p :=
  charP_of_injective_ringHom (PowerSeries.C_injective (R := ZMod p)) p

lemma ppow_ne (e : ℕ) : p ^ e ≠ 0 := pow_ne_zero _ hp.out.ne_zero

lemma frob_qfac (e N : ℕ) : (Ψ p (qfac N)) ^ (p ^ e) = Ψ p (Ea (p ^ e) (ppow_ne p e) (qfac N)) := by
  rw [Ψ, qfac, map_prod, map_prod, map_prod, ← prod_pow]
  refine prod_congr rfl fun i _ => ?_
  simp only [map_sub, map_one, map_pow, PowerSeries.map_X, Ea_X]
  rw [sub_pow_char_pow, one_pow, ← pow_mul, ← pow_mul, mul_comm]

lemma coeff_congr_of_dvd' {f g : PowerSeries (ZMod p)} {m : ℕ}
    (h : (X : PowerSeries (ZMod p)) ^ (m + 1) ∣ (f - g)) : coeff m f = coeff m g := by
  have := (PowerSeries.X_pow_dvd_iff.mp h) m (Nat.lt_succ_self m)
  rwa [map_sub, sub_eq_zero] at this

lemma X_pow_dvd_qfacInf_sub' (N : ℕ) : (X : PowerSeries ℤ) ^ N ∣ qfacInf - qfac N := by
  rw [PowerSeries.X_pow_dvd_iff]; intro j hj
  rw [map_sub, coeff_qfacInf (show j + 1 ≤ N by omega), sub_self]

lemma dvd_Ea {a N : ℕ} (ha : a ≠ 0) {f : PowerSeries ℤ} (h : (X : PowerSeries ℤ) ^ N ∣ f) :
    (X : PowerSeries ℤ) ^ N ∣ Ea a ha f := by
  obtain ⟨g, rfl⟩ := h
  rw [map_mul, map_pow, Ea_X, ← pow_mul]
  exact dvd_mul_of_dvd_left (pow_dvd_pow X (Nat.le_mul_of_pos_left N (Nat.pos_of_ne_zero ha))) _

lemma dvd_Ψ {N : ℕ} {f : PowerSeries ℤ} (h : (X : PowerSeries ℤ) ^ N ∣ f) :
    (X : PowerSeries (ZMod p)) ^ N ∣ Ψ p f := by
  obtain ⟨g, rfl⟩ := h
  exact ⟨Ψ p g, by rw [map_mul, map_pow, Ψ, PowerSeries.map_X]⟩

/-- **Frobenius**: `(q;q)_∞^{pᵉ} ≡ (q^{pᵉ};q^{pᵉ})_∞ (mod p)`. -/
lemma frob_qfacInf (e : ℕ) : (Ψ p qfacInf) ^ (p ^ e) = Ψ p (Ea (p ^ e) (ppow_ne p e) qfacInf) := by
  ext m
  have hqf : (X : PowerSeries (ZMod p)) ^ (m + 1) ∣ (Ψ p qfacInf - Ψ p (qfac (m + 1))) := by
    obtain ⟨g, hg⟩ := X_pow_dvd_qfacInf_sub' (m + 1)
    exact ⟨Ψ p g, by rw [← map_sub, hg, map_mul, map_pow, Ψ, PowerSeries.map_X]⟩
  have h5 : (X : PowerSeries (ZMod p)) ^ (m + 1) ∣ ((Ψ p qfacInf) ^ (p ^ e) - (Ψ p (qfac (m + 1))) ^ (p ^ e)) :=
    dvd_trans hqf (sub_dvd_pow_sub_pow _ _ _)
  have hE : (X : PowerSeries (ZMod p)) ^ (m + 1) ∣
      (Ψ p (Ea (p ^ e) (ppow_ne p e) qfacInf) - Ψ p (Ea (p ^ e) (ppow_ne p e) (qfac (m + 1)))) := by
    rw [← map_sub, ← map_sub]
    exact dvd_Ψ p (dvd_Ea (ppow_ne p e) (X_pow_dvd_qfacInf_sub' (m + 1)))
  rw [coeff_congr_of_dvd' p h5, frob_qfac, coeff_congr_of_dvd' p hE]

end Frob

/-! ## the cube coefficients -/

lemma tri_inj {b m : ℕ} (h : b * (b + 1) / 2 = m * (m + 1) / 2) : b = m := by
  have hb : b * (b + 1) = 2 * (b * (b + 1) / 2) := by
    obtain ⟨r, hr⟩ := Nat.even_mul_succ_self b; omega
  have hm : m * (m + 1) = 2 * (m * (m + 1) / 2) := by
    obtain ⟨r, hr⟩ := Nat.even_mul_succ_self m; omega
  have he : b * (b + 1) = m * (m + 1) := by omega
  rcases lt_trichotomy b m with hlt | heq | hgt
  · have : b * (b + 1) < m * (m + 1) := Nat.mul_lt_mul'' hlt (by omega)
    omega
  · exact heq
  · have : m * (m + 1) < b * (b + 1) := Nat.mul_lt_mul'' hgt (by omega)
    omega

lemma coeff_cube_tri (m : ℕ) : coeff (m * (m + 1) / 2) jacobiCubeSum = (-1 : ℤ) ^ m * (2 * m + 1) := by
  set y := m * (m + 1) / 2
  rw [coeff_jacobiCubeSum (le_refl (y + 1))]
  have hmy : m < y + 1 := by
    have : m * (m + 1) = 2 * y := by have := Nat.even_mul_succ_self m; obtain ⟨r, hr⟩ := this; omega
    nlinarith
  rw [sum_eq_single_of_mem m (mem_range.mpr hmy)]
  · rw [coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_C, if_pos rfl]
  · intro b _ hb
    rw [coeff_X_pow_mul']
    split_ifs with h
    · rw [coeff_C, if_neg]
      intro h0
      apply hb
      have : b * (b + 1) / 2 = y := by omega
      exact tri_inj this
    · rfl

/-- the cube coefficients are odd exactly at triangular numbers. -/
lemma cube_odd_iff (y : ℕ) : Odd (coeff y jacobiCubeSum) ↔ ∃ m, m * (m + 1) = 2 * y := by
  constructor
  · intro h
    obtain ⟨m, hm, -⟩ := coeff_jacobiCubeSum_value (fun h0 => by rw [h0] at h; exact Int.not_odd_zero h)
    exact ⟨m, by exact_mod_cast hm⟩
  · rintro ⟨m, hm⟩
    have hy : y = m * (m + 1) / 2 := by omega
    rw [hy, coeff_cube_tri]
    exact (odd_neg_one.pow).mul (odd_two_mul_add_one (m : ℤ))


/-! ## `τ` mod 2 -/

lemma Ψ2_tau : Ψ 2 (X * qfacInf ^ 24) = Ψ 2 (X * Ea (2 ^ 3) (ppow_ne 2 3) jacobiCubeSum) := by
  rw [← jacobi_cube_identity, map_mul, map_mul, show qfacInf ^ 24 = (qfacInf ^ (2 ^ 3)) ^ 3 by ring, map_pow,
    map_pow, frob_qfacInf 2 3, map_pow, map_pow]

lemma coeff_Ψ (p : ℕ) [Fact p.Prime] (n : ℕ) (f : PowerSeries ℤ) : coeff n (Ψ p f) = ((coeff n f : ℤ) : ZMod p) := by
  rw [Ψ, coeff_map]; rfl

/-- **`τ(n)` is odd iff `n` is an odd square.** -/
theorem tau_odd_iff (n : ℕ) : Odd (tauPS n) ↔ ∃ m, n = (2 * m + 1) ^ 2 := by
  have h := congrArg (coeff n) Ψ2_tau
  rw [coeff_Ψ, coeff_Ψ, ZMod.intCast_eq_intCast_iff'] at h
  simp only [Nat.cast_ofNat] at h
  rw [tauPS, Int.odd_iff, h, ← Int.odd_iff]
  rcases n with _ | k
  · simp only [coeff_zero_eq_constantCoeff, map_mul, constantCoeff_X, zero_mul]
    constructor
    · intro h0; exact absurd h0 (by decide)
    · rintro ⟨m, hm⟩; have : 0 < (2 * m + 1) ^ 2 := by positivity
      omega
  · rw [coeff_succ_X_mul, coeff_Ea]
    norm_num
    by_cases h8 : 8 ∣ k
    · rw [if_pos h8, cube_odd_iff]
      obtain ⟨c, rfl⟩ := h8
      rw [Nat.mul_div_cancel_left _ (by norm_num)]
      constructor
      · rintro ⟨m, hm⟩; exact ⟨m, by nlinarith⟩
      · rintro ⟨m, hm⟩; exact ⟨m, by nlinarith⟩
    · rw [if_neg h8]
      constructor
      · intro h0; exact absurd h0 (by decide)
      · rintro ⟨m, hm⟩
        exfalso; apply h8
        obtain ⟨r, hr⟩ := Nat.even_mul_succ_self m
        exact ⟨r, by nlinarith⟩

/-! ## `τ` mod 7 -/

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

lemma Ψ7_tau : Ψ 7 (X * qfacInf ^ 24)
    = Ψ 7 (X * (Ea (7 ^ 1) (ppow_ne 7 1) jacobiCubeSum * jacobiCubeSum)) := by
  rw [← jacobi_cube_identity, map_mul, map_mul, show qfacInf ^ 24 = (qfacInf ^ (7 ^ 1)) ^ 3 * qfacInf ^ 3 by ring,
    map_mul, map_pow, map_pow, frob_qfacInf 7 1]
  simp only [map_mul, map_pow]

/-- **Ramanujan: `τ(n) ≡ 0 (mod 7)` for `n ≡ 0, 3, 5, 6 (mod 7)`.** -/
theorem tau_mod7 {n : ℕ} (hn : n % 7 = 0 ∨ n % 7 = 3 ∨ n % 7 = 5 ∨ n % 7 = 6) : (7 : ℤ) ∣ tauPS n := by
  have h := congrArg (coeff n) Ψ7_tau
  rw [coeff_Ψ, coeff_Ψ] at h
  suffices hc : (7 : ℤ) ∣ coeff n (X * (Ea (7 ^ 1) (ppow_ne 7 1) jacobiCubeSum * jacobiCubeSum)) by
    have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr (by exact_mod_cast hc)
    rw [← h] at h1
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp h1
    rw [tauPS]; exact_mod_cast this
  rcases n with _ | k
  · simp
  rw [coeff_succ_X_mul, coeff_mul]
  refine dvd_sum fun x hx => ?_
  obtain ⟨i, j⟩ := x
  rw [mem_antidiagonal] at hx
  rw [coeff_Ea]
  norm_num
  by_cases h7 : 7 ∣ i
  · rw [if_pos h7]
    by_cases hj : coeff j jacobiCubeSum = 0
    · rw [hj, mul_zero]; exact dvd_zero _
    obtain ⟨m, hm, hval⟩ := coeff_jacobiCubeSum_value hj
    rw [hval]
    apply dvd_mul_of_dvd_right
    apply dvd_mul_of_dvd_right
    obtain ⟨a, rfl⟩ := h7
    have key : 8 * ((k + 1 : ℕ) : ℤ) = 56 * a + (2 * m + 1) ^ 2 + 7 := by
      have : ((k : ℕ) : ℤ) = 7 * a + j := by exact_mod_cast hx.symm
      push_cast
      linear_combination 8 * this - 4 * hm
    set s : ℤ := 2 * m + 1
    obtain ⟨t, r, hr0, hr7, hs⟩ : ∃ t r : ℤ, 0 ≤ r ∧ r < 7 ∧ s = 7 * t + r :=
      ⟨s / 7, s % 7, Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num), (Int.mul_ediv_add_emod s 7).symm⟩
    rw [hs, show (7 * t + r) ^ 2 = 7 * (7 * t ^ 2 + 2 * t * r) + r ^ 2 by ring] at key
    generalize 7 * t ^ 2 + 2 * t * r = W at key
    rw [hs]
    have hn' := hn
    interval_cases r <;> norm_num at key <;> omega
  · rw [if_neg h7]; simp


/-! ## `τ` mod 3 and mod 5 -/

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- **`τ(n) ≡ 0 (mod 3)` unless `n ≡ 1 (mod 3)`.** -/
theorem tau_mod3 {n : ℕ} (hn : n % 3 ≠ 1) : (3 : ℤ) ∣ tauPS n := by
  have hΨ : Ψ 3 (X * qfacInf ^ 24) = Ψ 3 (X * Ea (3 ^ 1) (ppow_ne 3 1) (qfacInf ^ 8)) := by
    rw [map_mul, map_mul, show qfacInf ^ 24 = (qfacInf ^ (3 ^ 1)) ^ 8 by ring, map_pow, map_pow, frob_qfacInf 3 1]
    simp only [map_pow]
  have h := congrArg (coeff n) hΨ
  rw [coeff_Ψ, coeff_Ψ] at h
  suffices hc : coeff n (X * Ea (3 ^ 1) (ppow_ne 3 1) (qfacInf ^ 8)) = 0 by
    rw [hc, Int.cast_zero, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    rw [tauPS]; exact_mod_cast h
  rcases n with _ | k
  · simp
  · rw [coeff_succ_X_mul, coeff_Ea, if_neg (by norm_num; omega)]

/-- **Ramanujan: `τ(5n) ≡ 0 (mod 5)`.** -/
theorem tau_mod5 {n : ℕ} (hn : n % 5 = 0) : (5 : ℤ) ∣ tauPS n := by
  have hΨ : Ψ 5 (X * qfacInf ^ 24) = Ψ 5 X * (Ψ 5 (Ea (5 ^ 1) (ppow_ne 5 1) (qfacInf ^ 4)) * Ψ5 (qfacInf ^ 4)) := by
    rw [map_mul, show qfacInf ^ 24 = (qfacInf ^ (5 ^ 1)) ^ 4 * qfacInf ^ 4 by ring, map_mul, map_pow, map_pow,
      frob_qfacInf 5 1]
    simp only [map_pow]; rfl
  have h := congrArg (coeff n) hΨ
  rw [coeff_Ψ] at h
  suffices hc : coeff n (Ψ 5 X * (Ψ 5 (Ea (5 ^ 1) (ppow_ne 5 1) (qfacInf ^ 4)) * Ψ5 (qfacInf ^ 4))) = 0 by
    rw [hc, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    rw [tauPS]; exact_mod_cast h
  rcases n with _ | k
  · simp [Ψ]
  rw [show Ψ 5 X = X by simp [Ψ], coeff_succ_X_mul, coeff_mul]
  refine sum_eq_zero fun x hx => ?_
  obtain ⟨i, j⟩ := x
  rw [mem_antidiagonal] at hx
  rw [coeff_Ψ, coeff_Ea]
  by_cases h5 : 5 ^ 1 ∣ i
  · obtain ⟨a, rfl⟩ := h5
    rw [coeff_qfac4_mod5 (by norm_num at hx ⊢; omega), mul_zero]
  · rw [if_neg h5]; simp


/-! ## `τ` mod 23 (Wilton) -/

instance : Fact (Nat.Prime 23) := ⟨by norm_num⟩

/-- **Wilton's congruence**: `τ(n) ≡ 0 (mod 23)` whenever `n` is a quadratic non-residue mod 23.
Here `q(q)²⁴ ≡ q (q²³;q²³)_∞ (q;q)_∞ (mod 23)`, and `24(1 + k(3k−1)/2) = (6k−1)² + 23` puts every exponent
in a square class mod 23. -/
theorem tau_mod23 {n : ℕ}
    (hn : n % 23 ∈ ({5, 7, 10, 11, 14, 15, 17, 19, 20, 21, 22} : Finset ℕ)) : (23 : ℤ) ∣ tauPS n := by
  have hΨ : Ψ 23 (X * qfacInf ^ 24)
      = Ψ 23 (X * (Ea (23 ^ 1) (ppow_ne 23 1) pentSeries * pentSeries)) := by
    rw [← euler_pentagonal, map_mul, show qfacInf ^ 24 = qfacInf ^ (23 ^ 1) * qfacInf by ring, map_mul, map_pow,
      frob_qfacInf 23 1]
    simp only [map_mul, map_pow]
  have h := congrArg (coeff n) hΨ
  rw [coeff_Ψ, coeff_Ψ] at h
  suffices hc : coeff n (X * (Ea (23 ^ 1) (ppow_ne 23 1) pentSeries * pentSeries)) = 0 by
    rw [hc, Int.cast_zero, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    rw [tauPS]; exact_mod_cast h
  rcases n with _ | k
  · simp
  rw [coeff_succ_X_mul, coeff_mul]
  refine sum_eq_zero fun x hx => ?_
  obtain ⟨i, j⟩ := x
  rw [mem_antidiagonal] at hx
  rw [coeff_Ea]
  simp only [pow_one]
  by_cases h23 : 23 ∣ i
  · rw [if_pos h23]
    by_cases hj : coeff j pentSeries = 0
    · rw [hj, mul_zero]
    exfalso
    obtain ⟨κ, hκ⟩ := coeff_pentSeries_support hj
    obtain ⟨a, rfl⟩ := h23
    have key : 24 * ((k + 1 : ℕ) : ℤ) = 552 * a + (6 * κ - 1) ^ 2 + 23 := by
      have : ((k : ℕ) : ℤ) = 23 * a + j := by exact_mod_cast hx.symm
      push_cast
      linear_combination 24 * this - 12 * hκ
    set s : ℤ := 6 * κ - 1
    obtain ⟨t, r, hr0, hr7, hs⟩ : ∃ t r : ℤ, 0 ≤ r ∧ r < 23 ∧ s = 23 * t + r :=
      ⟨s / 23, s % 23, Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num),
        (Int.mul_ediv_add_emod s 23).symm⟩
    rw [hs, show (23 * t + r) ^ 2 = 23 * (23 * t ^ 2 + 2 * t * r) + r ^ 2 by ring] at key
    generalize 23 * t ^ 2 + 2 * t * r = W at key
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    interval_cases r <;> norm_num at key <;> omega
  · rw [if_neg h23]; simp

end TauCong
