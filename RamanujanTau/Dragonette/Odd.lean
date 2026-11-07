/-
# The product `(−s;s²)_∞` and the modular transformation of `b(q)` at `q → −1`

* `Oz s = ∏_{k≥0} (1 + s^{2k+1})` satisfies `Oz(s)·(s;s)_∞·(s⁴;s⁴)_∞ = (s²;s²)_∞²` on the disc;
* hence, with `F = 1/(q;q)_∞` and its transformation `HardyRamanujan.F_modular`, for `Re z > 0`:
  `Oz(e^{−z}) = e^{π²/(24z) − z/24} · Fr z`, `Fr z = F(e^{−4π²/z}) F(e^{−π²/z}) (e^{−2π²/z};e^{−2π²/z})_∞²`;
* Ramanujan's `b(q) = (q;q²)_∞ Σ_ℤ(−1)ⁿq^{n²}` at `q = −e^{−z}` is `Oz(e^{−z})·Jt z`.
-/
import RamanujanTau.Dragonette.Theta
import RamanujanTau.HardyRamanujan.Main

set_option autoImplicit false

namespace Dragonette
open Complex Metric HardyRamanujan
open scoped Real

/-- `(−s;s²)_∞`. -/
noncomputable def Oz (s : ℂ) : ℂ := ∏' k : ℕ, (1 + s ^ (2 * k + 1))

lemma mult_one_add {s : ℂ} (hs : ‖s‖ < 1) {a : ℕ → ℂ} (ha : ∀ k, ‖a k‖ ≤ ‖s‖ ^ k) :
    Multipliable fun k => 1 + a k :=
  Complex.multipliable_one_add_of_summable
    (Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg _) hs) ha)

lemma norm_pow_le {s : ℂ} (hs : ‖s‖ < 1) {k m : ℕ} (h : k ≤ m) : ‖s ^ m‖ ≤ ‖s‖ ^ k := by
  rw [norm_pow]; exact pow_le_pow_of_le_one (norm_nonneg _) hs.le h

lemma mult_one_sub_pow {s : ℂ} (hs : ‖s‖ < 1) (e : ℕ → ℕ) (he : ∀ k, k ≤ e k) :
    Multipliable fun k => 1 - s ^ e k := by
  have := mult_one_add hs (a := fun k => -s ^ e k) fun k => by rw [norm_neg]; exact norm_pow_le hs (he k)
  simpa [sub_eq_add_neg] using this

lemma mult_one_add_pow {s : ℂ} (hs : ‖s‖ < 1) (e : ℕ → ℕ) (he : ∀ k, k ≤ e k) :
    Multipliable fun k => 1 + s ^ e k :=
  mult_one_add hs fun k => norm_pow_le hs (he k)

/-- **the product identity** `(−s;s²)_∞ (s;s)_∞ (s⁴;s⁴)_∞ = (s²;s²)_∞²`. -/
theorem Oz_mul {s : ℂ} (hs : ‖s‖ < 1) : Oz s * Pq s * Pq (s ^ 4) = Pq (s ^ 2) ^ 2 := by
  have hs2 : ‖s ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hs (by norm_num)
  -- `(s;s)_∞ = (s;s²)_∞ (s²;s²)_∞`
  have h1 : Pq s = (∏' k : ℕ, (1 - s ^ (2 * k + 1))) * Pq (s ^ 2) := by
    rw [Pq_eq, Pq_eq, ← tprod_even_mul_odd (f := fun n : ℕ => 1 - s ^ (n + 1))
      (mult_one_sub_pow hs (fun k => 2 * k + 1) (fun k => by dsimp only; omega))
      (by simpa using mult_one_sub_pow hs (fun k => 2 * k + 1 + 1) (fun k => by dsimp only; omega))]
    congr 1
    congr 1; funext k; rw [← pow_mul]; ring_nf
  -- `(s²;s²)_∞ = (s²;s⁴)_∞ (s⁴;s⁴)_∞`
  have h2 : Pq (s ^ 2) = (∏' k : ℕ, (1 - s ^ (4 * k + 2))) * Pq (s ^ 4) := by
    rw [Pq_eq, Pq_eq, ← tprod_even_mul_odd (f := fun n : ℕ => 1 - (s ^ 2) ^ (n + 1))
      (by simpa [← pow_mul] using mult_one_sub_pow hs (fun k => 2 * (2 * k + 1)) (fun k => by dsimp only; omega))
      (by simpa [← pow_mul] using mult_one_sub_pow hs (fun k => 2 * (2 * k + 1 + 1)) (fun k => by dsimp only; omega))]
    congr 1
    · congr 1; funext k; rw [← pow_mul]; ring_nf
    · congr 1; funext k; rw [← pow_mul, ← pow_mul]; ring_nf
  -- `(−s;s²)_∞ (s;s²)_∞ = (s²;s⁴)_∞`
  have h3 : Oz s * (∏' k : ℕ, (1 - s ^ (2 * k + 1))) = ∏' k : ℕ, (1 - s ^ (4 * k + 2)) := by
    rw [Oz, ← (mult_one_add_pow hs (fun k => 2 * k + 1) (fun k => by dsimp only; omega)).tprod_mul
      (mult_one_sub_pow hs (fun k => 2 * k + 1) (fun k => by dsimp only; omega))]
    congr 1; funext k
    rw [show 4 * k + 2 = 2 * (2 * k + 1) by ring, pow_mul']; ring
  rw [h1, h2, ← h3]
  ring

lemma exp_pow (z : ℂ) (m : ℕ) : cexp (-z) ^ m = cexp (-((m : ℂ) * z)) := by
  rw [← Complex.exp_nat_mul]; ring_nf

/-- `√(cz/2π) = √c · √(z/2π)` for `c > 0`. -/
lemma sq_mul {c : ℝ} (hc : 0 < c) {z : ℂ} (hz : z ≠ 0) :
    HardyRamanujan.sq ((c : ℂ) * z) = cexp (Real.log c / 2) * HardyRamanujan.sq z := by
  have hπ : (2 * π : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  unfold HardyRamanujan.sq
  rw [show (c : ℂ) * z / (2 * π) = (c : ℂ) * (z / (2 * π)) by ring,
    Complex.log_ofReal_mul hc (div_ne_zero hz hπ), ← Complex.exp_add]
  congr 1; ring

/-- `Fr z = F(e^{−4π²/z}) F(e^{−π²/z}) (e^{−2π²/z};e^{−2π²/z})_∞²`. -/
noncomputable def Fr (z : ℂ) : ℂ :=
  F (cexp (-(4 * π ^ 2 / z))) * F (cexp (-(π ^ 2 / z))) * Pq (cexp (-(2 * π ^ 2 / z))) ^ 2

/-- **the transformation of `(−s;s²)_∞`**: `Oz(e^{−z}) = e^{π²/(24z) − z/24} Fr z`. -/
theorem Oz_transform {z : ℂ} (hz : 0 < z.re) :
    Oz (cexp (-z)) = cexp (π ^ 2 / (24 * z) - z / 24) * Fr z := by
  have hz0 := re_ne hz
  set s := cexp (-z) with hs
  have hs1 : ‖s‖ < 1 := by rw [hs, norm_exp, neg_re, Real.exp_lt_one_iff]; linarith
  have hb : ∀ m : ℕ, 1 ≤ m → s ^ m ∈ ball (0 : ℂ) 1 := fun m hm => by
    rw [mem_ball_zero_iff, norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hs1 (by omega)
  have hP1 := Pq_ne_zero (by simpa using hb 1 le_rfl)
  have hP4 := Pq_ne_zero (hb 4 (by norm_num))
  have hO : Oz s = F s * F (s ^ 4) * Pq (s ^ 2) ^ 2 := by
    have := Oz_mul hs1
    rw [F, F]; field_simp; rw [← this]
  have h2z : 0 < (2 * z).re := by simp; linarith
  have h4z : 0 < (4 * z).re := by simp; linarith
  have e2 : s ^ 2 = cexp (-(2 * z)) := by rw [hs, exp_pow]; norm_num
  have e4 : s ^ 4 = cexp (-(4 * z)) := by rw [hs, exp_pow]; norm_num
  have hF1 := F_modular hz
  have hF4 := F_modular h4z
  have hF2 := F_modular h2z
  have hP2 : Pq (cexp (-(2 * z))) = (F (cexp (-(2 * z))))⁻¹ := by rw [F, inv_inv]
  rw [hO, e2, e4, hP2, hF1, hF4, hF2]
  have r4 : 4 * (π : ℂ) ^ 2 / (4 * z) = π ^ 2 / z := by field_simp
  have r2 : 4 * (π : ℂ) ^ 2 / (2 * z) = 2 * π ^ 2 / z := by field_simp; ring
  rw [r4, r2]
  have hsq4 : HardyRamanujan.sq (4 * z) = cexp (Real.log 4 / 2) * HardyRamanujan.sq z := by
    have := sq_mul (c := 4) (by norm_num) hz0; push_cast at this; exact this
  have hsq2 : HardyRamanujan.sq (2 * z) = cexp (Real.log 2 / 2) * HardyRamanujan.sq z := by
    have := sq_mul (c := 2) (by norm_num) hz0; push_cast at this; exact this
  rw [hsq4, hsq2]
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [hl4]
  unfold Fr
  simp only [F]
  have hsq0 : HardyRamanujan.sq z ≠ 0 := Complex.exp_ne_zero _
  have hA : ∀ w : ℂ, cexp w ≠ 0 := Complex.exp_ne_zero
  have hPa : Pq (cexp (-(2 * π ^ 2 / z))) ≠ 0 := Pq_ne_zero (by
    have := HardyRamanujan.norm_cexp_neg_lt_one (w := 2 * π ^ 2 / z) (by
      have := re_pi_sq_div_pos hz
      rw [show (2 : ℂ) * π ^ 2 / z = ((2 : ℝ) : ℂ) * (π ^ 2 / z) by push_cast; ring, re_ofReal_mul]; linarith)
    exact this)
  have key : cexp (π ^ 2 / (24 * z) - z / 24) = cexp (π ^ 2 / (6 * z) - z / 24) *
      cexp (π ^ 2 / (6 * (4 * z)) - 4 * z / 24) * (cexp (π ^ 2 / (6 * (2 * z)) - 2 * z / 24))⁻¹ ^ 2 := by
    rw [← Complex.exp_neg, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add]
    congr 1; field_simp; ring
  have key2 : cexp (↑(2 * Real.log 2) / 2) = cexp (↑(Real.log 2) / 2) ^ 2 := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [key, key2]
  field_simp

/-- `b(q)` of `MockTheta3Radial` at `q = −e^{−z}`. -/
theorem bA_neg {z : ℂ} (hz : 0 < z.re) :
    MockTheta3.Radial.bA (-cexp (-z)) = Oz (cexp (-z)) * Jt z := by
  rw [MockTheta3.Radial.bA, ← two_θA_sub_one hz, Realize.Pfun, Oz]
  congr 1
  congr 1; funext k
  rw [show 1 + 2 * k = 2 * k + 1 by ring, Odd.neg_pow ⟨k, rfl⟩]; ring

end Dragonette
