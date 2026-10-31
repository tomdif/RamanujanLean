import RamanujanTau.ThetaLift.EtaMultiplier
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# The rank-one Jacobi theta function with character `χ₁₂`

`Θ(τ,ζ) = Σ_x χ₁₂(x) e(x²τ/24 + xζ)` is a Jacobi form of weight `1/2` and index `6` with the eta
multiplier. The translation law is immediate, and the inversion law comes from Mathlib's functional
equation for `jacobiTheta₂` together with the Gauss sum of `χ₁₂`.
-/

set_option autoImplicit false

namespace RamanujanTau.ThetaLift
open Complex
open scoped Real

noncomputable section

/-- The character `(12/·)` on the integers. -/
def chiZ (x : ℤ) : ℤ :=
  if x % 12 = 1 ∨ x % 12 = 11 then 1 else if x % 12 = 5 ∨ x % 12 = 7 then -1 else 0

lemma chiZ_add_mul (x n : ℤ) : chiZ (x + 12 * n) = chiZ x := by
  unfold chiZ
  rw [Int.add_mul_emod_self_left]

/-- The rank-one theta function. -/
def chiTheta (τ ζ : ℂ) : ℂ := ∑' x : ℤ, (chiZ x : ℂ) * jacobiTheta₂_term x ζ (τ / 12)

lemma term_eq (x : ℤ) (ζ τ : ℂ) :
    jacobiTheta₂_term x ζ (τ / 12) = cexp (2 * π * I * (x ^ 2 * τ / 24 + x * ζ)) := by
  unfold jacobiTheta₂_term
  congr 1
  ring

lemma summable_term (ζ : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable fun x : ℤ => jacobiTheta₂_term x ζ (τ / 12) := by
  apply (summable_jacobiTheta₂_term_iff ζ (τ / 12)).mpr
  have : (τ / 12).im = τ.im / 12 := by simp
  rw [this]
  positivity

lemma summable_chi_term (ζ : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable fun x : ℤ => (chiZ x : ℂ) * jacobiTheta₂_term x ζ (τ / 12) := by
  refine Summable.of_norm_bounded (summable_term ζ hτ).norm fun x => ?_
  rw [norm_mul]
  have : ‖((chiZ x : ℤ) : ℂ)‖ ≤ 1 := by
    unfold chiZ
    split_ifs <;> simp
  exact mul_le_of_le_one_left (norm_nonneg _) this

/-- `x² ≡ 1 (mod 24)` on the support of `χ₁₂`. -/
lemma sq_sub_one_of_chi (x : ℤ) (h : chiZ x ≠ 0) : (24 : ℤ) ∣ x ^ 2 - 1 := by
  have hx : x % 12 = 1 ∨ x % 12 = 5 ∨ x % 12 = 7 ∨ x % 12 = 11 := by
    unfold chiZ at h
    split_ifs at h with h1 h2
    · omega
    · omega
    · exact absurd rfl h
  have hq : x = 12 * (x / 12) + x % 12 := (Int.mul_ediv_add_emod x 12).symm
  set q := x / 12
  rcases hx with h | h | h | h <;> rw [h] at hq <;> rw [hq]
  · exact ⟨6 * q ^ 2 + q, by ring⟩
  · exact ⟨6 * q ^ 2 + 5 * q + 1, by ring⟩
  · exact ⟨6 * q ^ 2 + 7 * q + 2, by ring⟩
  · exact ⟨6 * q ^ 2 + 11 * q + 5, by ring⟩

/-- **Translation.** -/
theorem chiTheta_add_one (τ ζ : ℂ) : chiTheta (τ + 1) ζ = e24 1 * chiTheta τ ζ := by
  unfold chiTheta
  rw [← tsum_mul_left]
  congr 1
  funext x
  by_cases h : chiZ x = 0
  · simp [h]
  obtain ⟨m, hm⟩ := sq_sub_one_of_chi x h
  rw [term_eq, term_eq, mul_left_comm]
  congr 1
  unfold e24
  rw [← Complex.exp_add]
  have hsq : ((x : ℂ)) ^ 2 = 24 * m + 1 := by
    have : x ^ 2 = 24 * m + 1 := by linarith
    exact_mod_cast this
  have h2 : (2 * π * I * ((x : ℂ) ^ 2 * (τ + 1) / 24 + x * ζ)) =
      2 * π * I * (((1 : ℤ) : ℂ)) / 24 + 2 * π * I * ((x : ℂ) ^ 2 * τ / 24 + x * ζ) +
        (m : ℂ) * (2 * π * I) := by
    rw [show (x : ℂ) ^ 2 * (τ + 1) / 24 = (x : ℂ) ^ 2 * τ / 24 + (x : ℂ) ^ 2 / 24 by ring, hsq]
    push_cast
    ring
  rw [h2, Complex.exp_add _ ((m : ℂ) * (2 * π * I)), Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The primitive twelfth root of unity. -/
def z12 : ℂ := cexp (2 * π * I / 12)

lemma z12_pow_twelve : z12 ^ 12 = 1 := by
  unfold z12
  rw [← Complex.exp_nat_mul]
  have : ((12 : ℕ) : ℂ) * (2 * π * I / 12) = 2 * π * I := by push_cast; ring
  rw [this, Complex.exp_two_pi_mul_I]

lemma z12_cyclo : z12 ^ 4 - z12 ^ 2 + 1 = 0 := by
  have hc : z12 ^ 2 + (z12 ^ 2)⁻¹ = 1 := by
    have h1 : z12 ^ 2 = cexp ((π / 3 : ℝ) * I) := by
      unfold z12
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [h1, ← Complex.exp_neg]
    have h2 : cexp (((π / 3 : ℝ) : ℂ) * I) + cexp (-(((π / 3 : ℝ) : ℂ) * I)) =
        2 * Complex.cos ((π / 3 : ℝ) : ℂ) := by
      rw [Complex.cos]
      ring_nf
    rw [h2, ← Complex.ofReal_cos, Real.cos_pi_div_three]
    norm_num
  have hne : z12 ^ 2 ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
  have := congrArg (· * z12 ^ 2) hc
  simp only [add_mul, inv_mul_cancel₀ hne, one_mul] at this
  linear_combination this


/-- The Gauss sum. -/
def gG : ℂ := z12 - z12 ^ 5 - z12 ^ 7 + z12 ^ 11

/-- The Gauss sum relation on residues. -/
lemma gauss_residues (r : ℕ) (hr : r < 12) :
    z12 ^ r - z12 ^ (5 * r) - z12 ^ (7 * r) + z12 ^ (11 * r) = (chiZ r : ℂ) * gG := by
  have h0 : z12 ^ 0 - z12 ^ 0 - z12 ^ 0 + z12 ^ 0 = ((0 : ℤ) : ℂ) * gG := by
    unfold gG
    push_cast
    linear_combination (0) * z12_cyclo
  have h1 : z12 ^ 1 - z12 ^ 5 - z12 ^ 7 + z12 ^ 11 = ((1 : ℤ) : ℂ) * gG := by
    unfold gG
    push_cast
    linear_combination (0) * z12_cyclo
  have h2 : z12 ^ 2 - z12 ^ 10 - z12 ^ 14 + z12 ^ 22 = ((0 : ℤ) : ℂ) * gG := by
    unfold gG
    push_cast
    linear_combination (z12^18 + z12^16 - z12^12 - 2*z12^10 - z12^8 + z12^4 + z12^2) * z12_cyclo
  have h3 : z12 ^ 3 - z12 ^ 15 - z12 ^ 21 + z12 ^ 33 = ((0 : ℤ) : ℂ) * gG := by
    unfold gG
    push_cast
    linear_combination (z12^29 + z12^27 - z12^23 - z12^21 - z12^11 - z12^9 + z12^5 + z12^3) * z12_cyclo
  have h4 : z12 ^ 4 - z12 ^ 20 - z12 ^ 28 + z12 ^ 44 = ((0 : ℤ) : ℂ) * gG := by
    unfold gG
    push_cast
    linear_combination (z12^40 + z12^38 - z12^34 - z12^32 + z12^28 + z12^26 - z12^24 - 2*z12^22 - z12^20 + z12^18 + z12^16 - z12^12 - z12^10 + z12^6 + z12^4) * z12_cyclo
  have h5 : z12 ^ 5 - z12 ^ 25 - z12 ^ 35 + z12 ^ 55 = ((-1 : ℤ) : ℂ) * gG := by
    unfold gG
    push_cast
    linear_combination (z12^51 + z12^49 - z12^45 - z12^43 + z12^39 + z12^37 - z12^33 - 2*z12^31 - z12^29 + z12^27 + 2*z12^25 + z12^23 - 2*z12^21 - 3*z12^19 - z12^17 + 2*z12^15 + 3*z12^13 + z12^11 - 2*z12^9 - 2*z12^7 + z12^3 + z12) * z12_cyclo
  have h6 : z12 ^ 6 - z12 ^ 30 - z12 ^ 42 + z12 ^ 66 = ((0 : ℤ) : ℂ) * gG := by
    unfold gG
    push_cast
    linear_combination (z12^62 + z12^60 - z12^56 - z12^54 + z12^50 + z12^48 - z12^44 - z12^42 - z12^26 - z12^24 + z12^20 + z12^18 - z12^14 - z12^12 + z12^8 + z12^6) * z12_cyclo
  have h7 : z12 ^ 7 - z12 ^ 35 - z12 ^ 49 + z12 ^ 77 = ((-1 : ℤ) : ℂ) * gG := by
    unfold gG
    push_cast
    linear_combination (z12^73 + z12^71 - z12^67 - z12^65 + z12^61 + z12^59 - z12^55 - z12^53 + z12^49 + z12^47 - z12^45 - 2*z12^43 - z12^41 + z12^39 + 2*z12^37 + z12^35 - z12^33 - 3*z12^31 - 2*z12^29 + z12^27 + 3*z12^25 + 2*z12^23 - z12^21 - 3*z12^19 - 2*z12^17 + z12^15 + 3*z12^13 + 2*z12^11 - z12^9 - 2*z12^7 - z12^5 + z12^3 + z12) * z12_cyclo
  have h8 : z12 ^ 8 - z12 ^ 40 - z12 ^ 56 + z12 ^ 88 = ((0 : ℤ) : ℂ) * gG := by
    unfold gG
    push_cast
    linear_combination (z12^84 + z12^82 - z12^78 - z12^76 + z12^72 + z12^70 - z12^66 - z12^64 + z12^60 + z12^58 - z12^54 - 2*z12^52 - z12^50 + z12^48 + 2*z12^46 + z12^44 - z12^42 - 2*z12^40 - z12^38 + z12^34 + z12^32 - z12^28 - z12^26 + z12^22 + z12^20 - z12^16 - z12^14 + z12^10 + z12^8) * z12_cyclo
  have h9 : z12 ^ 9 - z12 ^ 45 - z12 ^ 63 + z12 ^ 99 = ((0 : ℤ) : ℂ) * gG := by
    unfold gG
    push_cast
    linear_combination (z12^95 + z12^93 - z12^89 - z12^87 + z12^83 + z12^81 - z12^77 - z12^75 + z12^71 + z12^69 - z12^65 - z12^63 - z12^41 - z12^39 + z12^35 + z12^33 - z12^29 - z12^27 + z12^23 + z12^21 - z12^17 - z12^15 + z12^11 + z12^9) * z12_cyclo
  have h10 : z12 ^ 10 - z12 ^ 50 - z12 ^ 70 + z12 ^ 110 = ((0 : ℤ) : ℂ) * gG := by
    unfold gG
    push_cast
    linear_combination (z12^106 + z12^104 - z12^100 - z12^98 + z12^94 + z12^92 - z12^88 - z12^86 + z12^82 + z12^80 - z12^76 - z12^74 + z12^70 + z12^68 - z12^66 - 2*z12^64 - z12^62 + z12^60 + 2*z12^58 + z12^56 - z12^54 - 2*z12^52 - z12^50 + z12^48 + z12^46 - z12^42 - z12^40 + z12^36 + z12^34 - z12^30 - z12^28 + z12^24 + z12^22 - z12^18 - z12^16 + z12^12 + z12^10) * z12_cyclo
  have h11 : z12 ^ 11 - z12 ^ 55 - z12 ^ 77 + z12 ^ 121 = ((1 : ℤ) : ℂ) * gG := by
    unfold gG
    push_cast
    linear_combination (z12^117 + z12^115 - z12^111 - z12^109 + z12^105 + z12^103 - z12^99 - z12^97 + z12^93 + z12^91 - z12^87 - z12^85 + z12^81 + z12^79 - z12^75 - 2*z12^73 - z12^71 + z12^69 + 2*z12^67 + z12^65 - z12^63 - 2*z12^61 - z12^59 + z12^57 + 2*z12^55 + z12^53 - 2*z12^51 - 3*z12^49 - z12^47 + 2*z12^45 + 3*z12^43 + z12^41 - 2*z12^39 - 3*z12^37 - z12^35 + 2*z12^33 + 3*z12^31 + z12^29 - 2*z12^27 - 3*z12^25 - z12^23 + 2*z12^21 + 3*z12^19 + z12^17 - 2*z12^15 - 3*z12^13 - z12^11 + 2*z12^9 + 3*z12^7 + z12^5 - z12^3 - z12) * z12_cyclo
  interval_cases r
  · simpa [chiZ] using h0
  · simpa [chiZ] using h1
  · simpa [chiZ] using h2
  · simpa [chiZ] using h3
  · simpa [chiZ] using h4
  · simpa [chiZ] using h5
  · simpa [chiZ] using h6
  · simpa [chiZ] using h7
  · simpa [chiZ] using h8
  · simpa [chiZ] using h9
  · simpa [chiZ] using h10
  · simpa [chiZ] using h11

lemma z12_six : z12 ^ 6 = -1 := by linear_combination (z12 ^ 2 + 1) * z12_cyclo

lemma z12_ne : z12 ≠ 0 := Complex.exp_ne_zero _

/-- The Gauss sum is `√12`. -/
lemma gG_eq : gG = ((√12 : ℝ) : ℂ) := by
  have h5 : z12 ^ 5 = -z12⁻¹ := by
    field_simp [z12_ne]
    linear_combination z12_six
  have hsum : z12 + z12⁻¹ = ((√3 : ℝ) : ℂ) := by
    have hz : z12 = cexp (((π / 6 : ℝ) : ℂ) * I) := by
      unfold z12
      congr 1
      push_cast
      ring
    rw [hz, ← Complex.exp_neg]
    have h2 : cexp (((π / 6 : ℝ) : ℂ) * I) + cexp (-(((π / 6 : ℝ) : ℂ) * I)) =
        2 * Complex.cos ((π / 6 : ℝ) : ℂ) := by
      rw [Complex.cos]
      ring_nf
    rw [h2, ← Complex.ofReal_cos, Real.cos_pi_div_six]
    push_cast
    ring
  have hG : gG = 2 * (z12 + z12⁻¹) := by
    unfold gG
    have h7 : z12 ^ 7 = -z12 := by linear_combination z12 * z12_six
    have h11 : z12 ^ 11 = z12⁻¹ := by
      have : z12 ^ 11 = z12 ^ 5 * z12 ^ 6 := by ring
      rw [this, z12_six, h5]
      ring
    rw [h5, h7, h11]
    ring
  have hs : √12 = 2 * √3 := by
    rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num)]
  rw [hG, hsum, hs]
  push_cast
  ring

lemma z12_zpow_int (n : ℤ) (k : ℕ) : z12 ^ (n * k) = z12 ^ ((n % 12).toNat * k) := by
  have hq : n = 12 * (n / 12) + (((n % 12).toNat : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
    exact (Int.mul_ediv_add_emod n 12).symm
  have hz : (z12 : ℂ) ^ (12 : ℤ) = 1 := by
    exact_mod_cast z12_pow_twelve
  conv_lhs => rw [hq]
  rw [add_mul, zpow_add₀ z12_ne, mul_assoc, zpow_mul, hz, one_zpow, one_mul]
  exact_mod_cast rfl

/-- The Gauss sum relation for every integer. -/
lemma gauss_int (n : ℤ) :
    z12 ^ (n * (1 : ℕ)) - z12 ^ (n * (5 : ℕ)) - z12 ^ (n * (7 : ℕ)) + z12 ^ (n * (11 : ℕ)) =
      (chiZ n : ℂ) * gG := by
  have hr : (n % 12).toNat < 12 := by
    have h0 := Int.emod_nonneg n (by norm_num : (12 : ℤ) ≠ 0)
    have h1 := Int.emod_lt_of_pos n (by norm_num : (0 : ℤ) < 12)
    omega
  have hg := gauss_residues _ hr
  have hc : chiZ ((n % 12).toNat : ℤ) = chiZ n := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
    unfold chiZ
    rw [Int.emod_emod_of_dvd _ (dvd_refl _)]
  rw [hc] at hg
  rw [z12_zpow_int n 1, z12_zpow_int n 5, z12_zpow_int n 7, z12_zpow_int n 11, ← hg]
  ring_nf

lemma term_shift (n : ℤ) (ζ τ : ℂ) (k : ℕ) :
    jacobiTheta₂_term n (ζ + k / 12) τ = z12 ^ (n * k) * jacobiTheta₂_term n ζ τ := by
  unfold jacobiTheta₂_term z12
  rw [← Complex.exp_int_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The Gauss representation of `Θ`. -/
theorem chiTheta_mul_gG (ζ : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    gG * chiTheta τ ζ = jacobiTheta₂ (ζ + (1 : ℕ) / 12) (τ / 12) -
      jacobiTheta₂ (ζ + (5 : ℕ) / 12) (τ / 12) - jacobiTheta₂ (ζ + (7 : ℕ) / 12) (τ / 12) +
      jacobiTheta₂ (ζ + (11 : ℕ) / 12) (τ / 12) := by
  have hτ' : 0 < (τ / 12).im := by
    have : (τ / 12).im = τ.im / 12 := by simp
    rw [this]
    positivity
  have h := (((hasSum_jacobiTheta₂_term (ζ + (1 : ℕ) / 12) hτ').sub
    (hasSum_jacobiTheta₂_term (ζ + (5 : ℕ) / 12) hτ')).sub
    (hasSum_jacobiTheta₂_term (ζ + (7 : ℕ) / 12) hτ')).add
    (hasSum_jacobiTheta₂_term (ζ + (11 : ℕ) / 12) hτ')
  have h2 := (summable_chi_term ζ hτ).hasSum.mul_left gG
  have heq : (fun n : ℤ => gG * ((chiZ n : ℂ) * jacobiTheta₂_term n ζ (τ / 12))) =
      fun n : ℤ => jacobiTheta₂_term n (ζ + (1 : ℕ) / 12) (τ / 12) -
        jacobiTheta₂_term n (ζ + (5 : ℕ) / 12) (τ / 12) -
        jacobiTheta₂_term n (ζ + (7 : ℕ) / 12) (τ / 12) +
        jacobiTheta₂_term n (ζ + (11 : ℕ) / 12) (τ / 12) := by
    funext n
    rw [term_shift, term_shift, term_shift, term_shift]
    have hg := gauss_int n
    linear_combination (-jacobiTheta₂_term n ζ (τ / 12)) * hg
  rw [heq] at h2
  exact h2.unique h

/-- The inversion constant. -/
lemma inversion_const {τ : ℂ} (hτ : 0 < τ.im) :
    1 / (-I * ((-1 / τ) / 12)) ^ (1 / 2 : ℂ) = ((√12 : ℝ) : ℂ) * (sqrt τ * e24 (-3)) := by
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  have hB : (-I * τ).re = τ.im := by simp
  have hB0 : -I * τ ≠ 0 := mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hτ0
  have hA : -I * ((-1 / τ) / 12) = (((12 : ℝ) : ℂ) * (-I * τ))⁻¹ := by
    field_simp
    rw [Complex.I_sq]
    push_cast
    ring
  have harg : (-I * τ).arg ≠ Real.pi := by
    intro h
    have := Complex.arg_eq_pi_iff.mp h
    rw [hB] at this
    linarith [this.1]
  have hargm : (((12 : ℝ) : ℂ) * (-I * τ)).arg ≠ Real.pi := by
    rw [Complex.arg_real_mul _ (by norm_num)]
    exact harg
  have hlog : log (-I * τ) = log τ - Real.pi / 2 * I := by
    obtain ⟨a0, a1⟩ := arg_bounds hτ
    have hexp : cexp (log τ - Real.pi / 2 * I) = -I * τ := by
      rw [Complex.exp_sub, Complex.exp_log hτ0]
      have : cexp ((Real.pi : ℂ) / 2 * I) = I := by
        rw [show (Real.pi : ℂ) / 2 * I = ((Real.pi / 2 : ℝ) : ℂ) * I by push_cast; ring,
          Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
          Real.sin_pi_div_two]
        simp
      rw [this]
      field_simp
      rw [Complex.I_sq]
      ring
    rw [← hexp, Complex.log_exp]
    · simp [Complex.log_im]
      linarith [Real.pi_pos]
    · simp [Complex.log_im]
      linarith [Real.pi_pos]
  have hsqrtB : (-I * τ) ^ (1 / 2 : ℂ) = sqrt τ * e24 (-3) := by
    rw [Complex.cpow_def_of_ne_zero hB0, sqrt_exp_half hτ0, hlog]
    unfold e24
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hmul : (((12 : ℝ) : ℂ) * (-I * τ)) ^ (1 / 2 : ℂ) =
      ((12 : ℝ) : ℂ) ^ (1 / 2 : ℂ) * (-I * τ) ^ (1 / 2 : ℂ) := by
    have h120 : ((12 : ℝ) : ℂ) ≠ 0 := by norm_num
    rw [Complex.cpow_def_of_ne_zero (mul_ne_zero h120 hB0), Complex.cpow_def_of_ne_zero h120,
      Complex.cpow_def_of_ne_zero hB0, Complex.log_ofReal_mul (by norm_num) hB0, ← Complex.exp_add,
      Complex.ofReal_log (by norm_num)]
    congr 1
    ring
  have h12 : ((12 : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((√12 : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by norm_num)]
    norm_num
  rw [hA, Complex.inv_cpow _ _ hargm, one_div, inv_inv, hmul, h12, hsqrtB]

/-- The dual terms attached to a residue. -/
def dualSum (ℓ : ℤ) (τ ζ : ℂ) : ℂ := ∑' n : ℤ, jacobiTheta₂_term (ℓ - 12 * n) ζ (τ / 12)

/-- Inversion for a single shifted `θ`. -/
lemma theta_inversion (ℓ : ℕ) {τ : ℂ} (hτ : 0 < τ.im) (ζ : ℂ) :
    jacobiTheta₂ (ζ / τ + (ℓ : ℕ) / 12) ((-1 / τ) / 12) =
      ((√12 : ℝ) : ℂ) * (sqrt τ * e24 (-3)) * cexp (2 * π * I * (6 * ζ ^ 2 / τ)) *
        dualSum ℓ τ ζ := by
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  rw [jacobiTheta₂_functional_equation, inversion_const hτ]
  have h1 : (ζ / τ + (ℓ : ℂ) / 12) / ((-1 / τ) / 12) = -12 * ζ - ℓ * τ := by
    field_simp
    ring
  have h2 : -1 / ((-1 / τ) / 12) = 12 * τ := by
    field_simp
  rw [h1, h2]
  have key : cexp (-π * I * (ζ / τ + (ℓ : ℂ) / 12) ^ 2 / ((-1 / τ) / 12)) *
      jacobiTheta₂ (-12 * ζ - ℓ * τ) (12 * τ) =
      cexp (2 * π * I * (6 * ζ ^ 2 / τ)) * dualSum ℓ τ ζ := by
    rw [show jacobiTheta₂ (-12 * ζ - ℓ * τ) (12 * τ) =
      ∑' n : ℤ, jacobiTheta₂_term n (-12 * ζ - ℓ * τ) (12 * τ) from rfl, dualSum, ← tsum_mul_left,
      ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    unfold jacobiTheta₂_term
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  rw [mul_assoc, key]
  ring

/-- Splitting a sum by residues modulo twelve. -/
lemma tsum_residues {f : ℤ → ℂ} (hf : Summable f) :
    ∑' x, f x = ∑ r : Fin 12, ∑' q : ℤ, f (q * ((12 : ℕ) : ℤ) + (r : ℕ)) := by
  let e : Fin 12 × ℤ ≃ ℤ := (Equiv.prodComm (Fin 12) ℤ).trans (Int.divModEquiv 12).symm
  have he : ∀ r q, e (r, q) = q * ((12 : ℕ) : ℤ) + (r : ℕ) := fun r q => rfl
  have hs : Summable (f ∘ e) := e.summable_iff.mpr hf
  rw [← e.tsum_eq f]
  have := hs.tsum_prod' (fun r => hs.prod_factor r)
  simp only [Function.comp] at this
  rw [this, tsum_fintype]
  refine Finset.sum_congr rfl fun r _ => tsum_congr fun q => ?_
  rw [he]

lemma chiZ_mul_add (q : ℤ) (r : ℕ) : chiZ (q * ((12 : ℕ) : ℤ) + r) = chiZ r := by
  rw [add_comm, mul_comm]
  exact chiZ_add_mul _ q

/-- `Θ` in terms of the four dual sums. -/
lemma chiTheta_eq_dual (ζ : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    chiTheta τ ζ = dualSum (1 : ℕ) τ ζ - dualSum (5 : ℕ) τ ζ - dualSum (7 : ℕ) τ ζ +
      dualSum (11 : ℕ) τ ζ := by
  have hres : ∀ r : ℕ, ∑' q : ℤ, (chiZ (q * ((12 : ℕ) : ℤ) + r) : ℂ) *
      jacobiTheta₂_term (q * ((12 : ℕ) : ℤ) + r) ζ (τ / 12) = (chiZ r : ℂ) * dualSum r τ ζ := by
    intro r
    simp only [chiZ_mul_add]
    rw [tsum_mul_left, dualSum]
    congr 1
    rw [← (Equiv.neg ℤ).tsum_eq]
    refine tsum_congr fun n => ?_
    congr 1
    simp
    ring
  rw [chiTheta, tsum_residues (summable_chi_term ζ hτ)]
  simp only [hres]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  have hc : ∀ r : ℕ, r < 12 → ((chiZ r : ℤ) : ℂ) = (chiZ r : ℤ) := fun _ _ => rfl
  simp [chiZ]
  ring

/-- **Inversion.** -/
theorem chiTheta_inversion (ζ : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    chiTheta (-1 / τ) (ζ / τ) =
      sqrt τ * e24 (-3) * cexp (2 * π * I * (6 * ζ ^ 2 / τ)) * chiTheta τ ζ := by
  have hG : gG ≠ 0 := by
    rw [gG_eq]
    have : √12 ≠ 0 := by positivity
    exact_mod_cast this
  have hτ' : 0 < (-1 / τ).im := by
    have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
    have hn : 0 < normSq τ := Complex.normSq_pos.mpr hτ0
    simp only [neg_div, one_div, neg_im, inv_im, neg_neg]
    exact div_pos hτ hn
  apply mul_left_cancel₀ hG
  rw [chiTheta_mul_gG _ hτ', theta_inversion 1 hτ, theta_inversion 5 hτ, theta_inversion 7 hτ,
    theta_inversion 11 hτ, chiTheta_eq_dual ζ hτ, gG_eq]
  ring

open Rademacher ModularForm MatrixGroups

/-- Composition of Möbius maps. -/
lemma mob_mul (γ δ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : mob (γ * δ) z = mob γ (mob δ z) := by
  have hL := denom_ne_zero' δ hz
  have hX := denom_ne_zero' γ (mob_im_pos δ hz)
  unfold mob at hX ⊢
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rw [div_eq_div_iff (by
    have := denom_ne_zero' (γ * δ) hz
    simpa [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] using this) hX]
  push_cast
  field_simp
  ring

/-- The cocycle of the denominator. -/
lemma lin_mul (γ δ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    lin (γ * δ) z = lin γ (mob δ z) * lin δ z := by
  have hL := denom_ne_zero' δ hz
  unfold lin mob
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  field_simp
  ring

/-- The Jacobi covariance, normalized by `η` so that no multiplier appears. -/
def ThetaLaw (γ : SL(2, ℤ)) : Prop :=
  ∀ (τ ζ : ℂ), 0 < τ.im → chiTheta (mob γ τ) (ζ / lin γ τ) * η τ =
    cexp (2 * π * I * (6 * (γ 1 0 : ℂ) * ζ ^ 2 / lin γ τ)) * chiTheta τ ζ * η (mob γ τ)

lemma thetaLaw_S : ThetaLaw sS := by
  intro τ ζ hτ
  have hm : mob sS τ = -1 / τ := by simp [mob, sS]
  have hl : lin sS τ = τ := by simp [lin, sS]
  have hc : sS 1 0 = 1 := rfl
  rw [hm, hl, hc, chiTheta_inversion ζ hτ, eta_S τ hτ]
  push_cast
  ring_nf

lemma thetaLaw_T : ThetaLaw (tr 1) := by
  intro τ ζ hτ
  have hm : mob (tr 1) τ = τ + (1 : ℤ) := by simp [mob, tr]
  have hl : lin (tr 1) τ = 1 := by simp [lin, tr]
  have hc : tr 1 1 0 = 0 := rfl
  rw [hm, hl, hc, eta_add_int]
  push_cast
  rw [chiTheta_add_one]
  simp
  ring

lemma thetaLaw_mul {γ δ : SL(2, ℤ)} (hγ : ThetaLaw γ) (hδ : ThetaLaw δ) : ThetaLaw (γ * δ) := by
  intro τ ζ hτ
  have hdet : δ 0 0 * δ 1 1 - δ 0 1 * δ 1 0 = 1 := by
    have h := δ.property
    rwa [Matrix.det_fin_two] at h
  have hτ1 := mob_im_pos δ hτ
  have hL : lin δ τ ≠ 0 := denom_ne_zero' δ hτ
  have hL1 : lin γ (mob δ τ) ≠ 0 := denom_ne_zero' γ hτ1
  have h1 := hδ τ ζ hτ
  have h2 := hγ (mob δ τ) (ζ / lin δ τ) hτ1
  have hη := eta_ne_zero hτ1
  have hzz : ζ / (lin γ (mob δ τ) * lin δ τ) = ζ / lin δ τ / lin γ (mob δ τ) := by
    field_simp
  rw [mob_mul γ δ hτ, lin_mul γ δ hτ, hzz]
  apply mul_right_cancel₀ hη
  have hexp : cexp (2 * π * I * (6 * ((γ * δ) 1 0 : ℂ) * ζ ^ 2 / (lin γ (mob δ τ) * lin δ τ))) =
      cexp (2 * π * I * (6 * (γ 1 0 : ℂ) * (ζ / lin δ τ) ^ 2 / lin γ (mob δ τ))) *
        cexp (2 * π * I * (6 * (δ 1 0 : ℂ) * ζ ^ 2 / lin δ τ)) := by
    rw [← Complex.exp_add]
    congr 1
    have hentry : (((γ * δ) 1 0 : ℤ) : ℂ) = (γ 1 0 : ℂ) * δ 0 0 + (γ 1 1 : ℂ) * δ 1 0 := by
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    have hdetC : (δ 0 0 : ℂ) * δ 1 1 - δ 0 1 * δ 1 0 = 1 := by exact_mod_cast hdet
    have hlin : lin γ (mob δ τ) * lin δ τ =
        (γ 1 0 : ℂ) * ((δ 0 0 : ℂ) * τ + δ 0 1) + (γ 1 1 : ℂ) * lin δ τ := by
      have hm : mob δ τ = ((δ 0 0 : ℂ) * τ + δ 0 1) / lin δ τ := rfl
      rw [hm]
      change ((γ 1 0 : ℂ) * (((δ 0 0 : ℂ) * τ + δ 0 1) / lin δ τ) + γ 1 1) * lin δ τ = _
      rw [add_mul, mul_assoc, div_mul_cancel₀ _ hL]
    have hLe : lin δ τ = (δ 1 0 : ℂ) * τ + δ 1 1 := rfl
    have hrel : ((γ 1 0 : ℂ) * δ 0 0 + (γ 1 1 : ℂ) * δ 1 0) * lin δ τ =
        (γ 1 0 : ℂ) + (δ 1 0 : ℂ) * (lin γ (mob δ τ) * lin δ τ) := by
      rw [hlin]
      have : (δ 0 0 : ℂ) * lin δ τ = 1 + (δ 1 0 : ℂ) * ((δ 0 0 : ℂ) * τ + δ 0 1) := by
        rw [hLe]
        linear_combination hdetC
      linear_combination (γ 1 0 : ℂ) * this
    have hfrac : ((γ 1 0 : ℂ) * δ 0 0 + (γ 1 1 : ℂ) * δ 1 0) / (lin γ (mob δ τ) * lin δ τ) =
        (γ 1 0 : ℂ) / (lin γ (mob δ τ) * lin δ τ ^ 2) + (δ 1 0 : ℂ) / lin δ τ := by
      rw [div_add_div _ _ (mul_ne_zero hL1 (pow_ne_zero 2 hL)) hL, div_eq_div_iff (mul_ne_zero hL1 hL)
        (mul_ne_zero (mul_ne_zero hL1 (pow_ne_zero 2 hL)) hL)]
      linear_combination (lin γ (mob δ τ) * lin δ τ ^ 2) * hrel
    rw [hentry]
    calc 2 * π * I * (6 * ((γ 1 0 : ℂ) * δ 0 0 + (γ 1 1 : ℂ) * δ 1 0) * ζ ^ 2 /
          (lin γ (mob δ τ) * lin δ τ))
        = 2 * π * I * (6 * ζ ^ 2) * (((γ 1 0 : ℂ) * δ 0 0 + (γ 1 1 : ℂ) * δ 1 0) /
          (lin γ (mob δ τ) * lin δ τ)) := by ring
      _ = _ := by
          rw [hfrac, div_pow]
          field_simp
  rw [hexp]
  linear_combination η τ * h2 + cexp (2 * π * I * (6 * (γ 1 0 : ℂ) * (ζ / lin δ τ) ^ 2 /
    lin γ (mob δ τ))) * η (mob γ (mob δ τ)) * h1

lemma mob_one (z : ℂ) : mob 1 z = z := by simp [mob]
lemma lin_one (z : ℂ) : lin 1 z = 1 := by simp [lin]

lemma thetaLaw_one : ThetaLaw 1 := by
  intro τ ζ _
  rw [mob_one, lin_one]
  simp

lemma thetaLaw_inv {γ : SL(2, ℤ)} (hγ : ThetaLaw γ) : ThetaLaw γ⁻¹ := by
  intro τ ζ hτ
  have hτ0 := mob_im_pos γ⁻¹ hτ
  have hmob : mob γ (mob γ⁻¹ τ) = τ := by
    rw [← mob_mul γ γ⁻¹ hτ, mul_inv_cancel, mob_one]
  have hprod : lin γ (mob γ⁻¹ τ) * lin γ⁻¹ τ = 1 := by
    rw [← lin_mul γ γ⁻¹ hτ, mul_inv_cancel, lin_one]
  have hL : lin γ⁻¹ τ ≠ 0 := denom_ne_zero' γ⁻¹ hτ
  have hc : ((γ⁻¹ 1 0 : ℤ) : ℂ) = -(γ 1 0 : ℂ) := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    simp
  have h := hγ (mob γ⁻¹ τ) (ζ / lin γ⁻¹ τ) hτ0
  have hL1 : lin γ (mob γ⁻¹ τ) = (lin γ⁻¹ τ)⁻¹ := eq_inv_of_mul_eq_one_left hprod
  have hz : ζ / lin γ⁻¹ τ / lin γ (mob γ⁻¹ τ) = ζ := by
    rw [hL1]
    field_simp
  rw [hmob, hz] at h
  have hexp : 6 * (γ 1 0 : ℂ) * (ζ / lin γ⁻¹ τ) ^ 2 / lin γ (mob γ⁻¹ τ) =
      6 * (γ 1 0 : ℂ) * ζ ^ 2 / lin γ⁻¹ τ := by
    rw [hL1]
    field_simp
  rw [hexp] at h
  rw [hc]
  have hE : cexp (2 * π * I * (6 * (-(γ 1 0 : ℂ)) * ζ ^ 2 / lin γ⁻¹ τ)) *
      cexp (2 * π * I * (6 * (γ 1 0 : ℂ) * ζ ^ 2 / lin γ⁻¹ τ)) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    ring
  linear_combination (-(cexp (2 * π * I * (6 * (-(γ 1 0 : ℂ)) * ζ ^ 2 / lin γ⁻¹ τ)))) * h -
    chiTheta (mob γ⁻¹ τ) (ζ / lin γ⁻¹ τ) * η τ * hE

/-- **The Jacobi covariance of `Θ/η` on all of `SL₂(ℤ)`.** -/
theorem thetaLaw (γ : SL(2, ℤ)) : ThetaLaw γ := by
  have hmem : γ ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]
    trivial
  induction hmem using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact thetaLaw_S
    · exact thetaLaw_T
  | one => exact thetaLaw_one
  | mul x y _ _ hx hy => exact thetaLaw_mul hx hy
  | inv x _ hx => exact thetaLaw_inv hx

end

end RamanujanTau.ThetaLift
