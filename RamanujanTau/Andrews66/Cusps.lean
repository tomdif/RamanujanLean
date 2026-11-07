/-
# M-a (first half): the transformation of `b(q) = (q;q)³_∞/(q²;q²)²_∞` at every cusp

`b = F(q²)²/F(q)³` with `F = 1/(q;q)_∞` (`bE`). Write `q = qp h k z = e^{2πi(h+iz)/k}`, `Re z > 0`.

* **even denominators** (`b_transform_even`): if `2k ∣ hh' + 1` then, with `|ω| = 1`,
  `b(e^{2πi(h+iz)/2k}) = ω z^{−1/2} e^{π(1/z − z)/(24k)} b(e^{2πi(h'+i/z)/2k})`.
  So near `h/2k` the eta quotient `b` has the growing main term `ω z^{−1/2} e^{π/(24kz)}` (since `b(q') → 1`):
  these are exactly the cusps carrying Andrews' terms (`2k`, `k ≤ √n`), with exponent `π/(24k z)`
  giving the Bessel argument `π√(24n−1)/(12k)`.
* **odd denominators** (`b_transform_odd`): if `k ∣ hh' + 1` and `k ∣ 2hh₂ + 1` then
  `b(e^{2πi(h+iz)/k}) = ω · 2z^{−1/2} e^{−π(2/z + z)/(12k)} F(Q₂)²/F(Q₁)³`, `Q₁ = e^{2πi(h'+i/z)/k}`,
  `Q₂ = e^{2πi(h₂+i/(2z))/k}`: `b` **decays** like `e^{−π/(6kz)}` at odd cusps.

Both are two applications of the general `η`-transformation `Rademacher.F_transform`.
-/
import RamanujanTau.Rademacher.FTransform
import RamanujanTau.Rademacher.Chord
import RamanujanTau.Rademacher.DedekindOmega

set_option autoImplicit false

namespace Andrews66
open Complex Metric
open scoped Real

noncomputable section

/-- `b(q) = (q;q)³_∞/(q²;q²)²_∞ = F(q²)²/F(q)³`. -/
def bE (q : ℂ) : ℂ := HardyRamanujan.F (q ^ 2) ^ 2 / HardyRamanujan.F q ^ 3

lemma qp_sq (h : ℤ) (k : ℕ) (w : ℂ) : Rademacher.qp h (2 * k) w ^ 2 = Rademacher.qp h k w := by
  unfold Rademacher.qp
  rw [← Complex.exp_nat_mul]
  congr 1
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    push_cast; field_simp

lemma qp_eq (h : ℤ) (k : ℕ) (z : ℂ) :
    cexp (2 * π * I * ((h + I * z) / k)) = Rademacher.qp h k z := rfl

lemma qp_inv_eq (h : ℤ) (k : ℕ) (z : ℂ) :
    cexp (2 * π * I * ((h + I / z) / k)) = Rademacher.qp h k (1 / z) := by
  unfold Rademacher.qp; rw [mul_one_div]

lemma F_qp_ne {h : ℤ} {k : ℕ} (hk : 0 < k) {w : ℂ} (hw : 0 < w.re) : HardyRamanujan.F (Rademacher.qp h k w) ≠ 0 :=
  Rademacher.F_ne_zero (Rademacher.qp_mem hk hw)

lemma sqrt_ne {z : ℂ} (hz : 0 < z.re) : Complex.sqrt z ≠ 0 := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  rw [sqrt_eq_exp hz0]; exact Complex.exp_ne_zero _

lemma sqrt_sq' {z : ℂ} (hz0 : z ≠ 0) : Complex.sqrt z ^ 2 = z := by
  rw [sqrt_eq_exp hz0, ← Complex.exp_nat_mul]
  rw [show ((2 : ℕ) : ℂ) * (log z / 2) = log z by push_cast; ring, exp_log hz0]

lemma inv_re_pos {z : ℂ} (hz : 0 < z.re) : 0 < (1 / z).re := Rademacher.re_inv_pos hz

/-- **the transformation of `b` at an even-denominator cusp `h/2k`**. -/
theorem b_transform_even {h h' : ℤ} {k : ℕ} (hk : 0 < k) (hdvd : ((2 * k : ℕ) : ℤ) ∣ h * h' + 1) :
    ∃ ω : ℂ, ‖ω‖ = 1 ∧ ∀ z : ℂ, 0 < z.re →
      bE (Rademacher.qp h (2 * k) z) =
        ω / Complex.sqrt z * cexp (π * (1 / z - z) / (24 * k)) * bE (Rademacher.qp h' (2 * k) (1 / z)) := by
  have hk2 : (0 : ℤ) < ((2 * k : ℕ) : ℤ) := by exact_mod_cast (by omega : 0 < 2 * k)
  have hk1 : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
  have hdvd1 : (k : ℤ) ∣ h * h' + 1 := (Int.natCast_dvd_natCast.mpr (Dvd.intro_left 2 rfl)).trans hdvd
  obtain ⟨ω₁, hω₁, H₁⟩ := Rademacher.F_transform hk2 hdvd
  obtain ⟨ω₂, hω₂, H₂⟩ := Rademacher.F_transform hk1 hdvd1
  refine ⟨ω₂ ^ 2 / ω₁ ^ 3, by rw [norm_div, norm_pow, norm_pow, hω₁, hω₂]; norm_num, fun z hz => ?_⟩
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have h1 := H₁ z hz
  have h2 := H₂ z hz
  simp only [Int.cast_natCast, qp_eq, qp_inv_eq] at h1 h2
  have hω₁0 : ω₁ ≠ 0 := fun h => by rw [h, norm_zero] at hω₁; norm_num at hω₁
  have hs := sqrt_ne hz
  have hF1 := F_qp_ne (h := h') (by omega : 0 < 2 * k) (inv_re_pos hz)
  have hF0 := F_qp_ne (h := h) (by omega : 0 < 2 * k) hz
  unfold bE
  rw [qp_sq, qp_sq, h2, h1]
  push_cast
  have hE : cexp (π * (1 / z - z) / (24 * k)) =
      cexp (π * (1 / z - z) / (12 * k)) ^ 2 / cexp (π * (1 / z - z) / (12 * (2 * k))) ^ 3 := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_sub]
    congr 1
    have : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    push_cast; field_simp; try ring
  rw [hE]
  have hsq := sqrt_sq' hz0
  have hs3 : Complex.sqrt z ^ 3 = z * Complex.sqrt z := by rw [pow_succ, hsq]
  have he1 : cexp (π * (1 / z - z) / (12 * (2 * k))) ≠ 0 := Complex.exp_ne_zero _
  rw [show (12 : ℂ) * (2 * (k : ℂ)) = 12 * (2 * (k : ℂ)) from rfl] at *
  field_simp

/-- **the transformation of `b` at an odd-denominator cusp `h/k`**: `b` decays like `e^{−π/(6k z)}`. -/
theorem b_transform_odd {h h' h₂ : ℤ} {k : ℕ} (hk : 0 < k) (hd1 : (k : ℤ) ∣ h * h' + 1)
    (hd2 : (k : ℤ) ∣ (2 * h) * h₂ + 1) :
    ∃ ω : ℂ, ‖ω‖ = 1 ∧ ∀ z : ℂ, 0 < z.re →
      bE (Rademacher.qp h k z) =
        ω * (2 / Complex.sqrt z) * cexp (-(π * (2 / z + z) / (12 * k))) *
          (HardyRamanujan.F (Rademacher.qp h₂ k (1 / (2 * z))) ^ 2 /
            HardyRamanujan.F (Rademacher.qp h' k (1 / z)) ^ 3) := by
  have hk1 : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
  obtain ⟨ω₁, hω₁, H₁⟩ := Rademacher.F_transform hk1 hd1
  obtain ⟨ω₂, hω₂, H₂⟩ := Rademacher.F_transform hk1 hd2
  refine ⟨ω₂ ^ 2 / ω₁ ^ 3, by rw [norm_div, norm_pow, norm_pow, hω₁, hω₂]; norm_num, fun z hz => ?_⟩
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have h2z : 0 < (2 * z).re := by simp; linarith
  have h1 := H₁ z hz
  have h2 := H₂ (2 * z) h2z
  simp only [Int.cast_natCast, qp_eq, qp_inv_eq] at h1 h2
  have hq2 : Rademacher.qp h k z ^ 2 = Rademacher.qp ((2 * h : ℤ)) k (2 * z) := by
    unfold Rademacher.qp
    rw [← Complex.exp_nat_mul]
    congr 1
    have : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    push_cast; field_simp
  have hω₁0 : ω₁ ≠ 0 := fun h => by rw [h, norm_zero] at hω₁; norm_num at hω₁
  have hs := sqrt_ne hz
  have hF1 := F_qp_ne (h := h') hk (inv_re_pos hz)
  have hF0 := F_qp_ne (h := h) hk hz
  unfold bE
  rw [hq2, h2, h1]
  push_cast
  have hE : cexp (-(π * (2 / z + z) / (12 * k))) =
      cexp (π * (1 / (2 * z) - 2 * z) / (12 * k)) ^ 2 / cexp (π * (1 / z - z) / (12 * k)) ^ 3 := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_sub]
    congr 1
    have : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    push_cast; field_simp; try ring
  rw [hE]
  have h2z0 : (2 : ℂ) * z ≠ 0 := mul_ne_zero two_ne_zero hz0
  have hsq := sqrt_sq' hz0
  have hsq2 := sqrt_sq' h2z0
  have hs3 : Complex.sqrt z ^ 3 = z * Complex.sqrt z := by rw [pow_succ, hsq]
  have he1 : cexp (π * (1 / z - z) / (12 * k)) ≠ 0 := Complex.exp_ne_zero _
  field_simp
  rw [hsq2, hsq]
  ring

end

end Andrews66
