/-
# Bounds for `G` and for the lattice theta function on the fundamental domain

* `exists_G_exp_le`: `G(z) ≤ K e^{−c Im z}` for `Im z ≥ 1/2` (cusp decay of `Δ`);
* `Qf_ge`: on `𝓕` (`|x| ≤ ½`, `x² + y² ≥ 1`), `Q(m,n) ≥ (m² + n²)/(2y)`;
* `theta_one_le`: `Θ_z(1) ≤ 2y·ϑ₀²` on `𝓕`, where `ϑ₀ = ∑ₖ e^{−πk²}`;
* `theta_sub_one_le`: `Θ_z(t) − 1 ≤ e^{−π(t−1)/(2y)} Θ_z(1)` for `t ≥ 1`;
* `theta_le_of_le_one`: `Θ_z(t) ≤ Θ_z(1)/t` for `0 < t ≤ 1`.
-/
import RamanujanTau.RankinError.Theta
import RamanujanTau.EisensteinReal.HoroIdent

set_option autoImplicit false

namespace RamanujanTau.RankinError

open Real Filter Topology MeasureTheory Set
open RamanujanTau.RankinSelberg RamanujanTau.EisensteinReal.Horo
open UpperHalfPlane hiding I
open scoped MatrixGroups

lemma exists_G_exp_le : ∃ K c : ℝ, 0 ≤ K ∧ 0 < c ∧ ∀ z : ℍ, 1 / 2 ≤ z.im →
    G z ≤ K * Real.exp (-c * z.im) := by
  obtain ⟨c, hc, hO⟩ := CuspFormClass.exp_decay_atImInfty' (CuspForm.discriminant : CuspForm 𝒮ℒ 12)
  obtain ⟨C, hC⟩ := hO.bound
  obtain ⟨A, hA⟩ := (atImInfty_mem _).1 hC
  obtain ⟨M, hM0, hM⟩ := exists_G_le
  set c₁ := c / 2 with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  set A' := max A 1
  refine ⟨|C| ^ 2 * (Nat.factorial 12 : ℝ) / c₁ ^ 12 + M * Real.exp (c₁ * A'), c₁, by positivity,
    hc₁0, fun z hz => ?_⟩
  have hy0 : 0 < z.im := z.im_pos
  rcases le_or_gt A' z.im with h | h
  · have hb := hA z ((le_max_left _ _).trans h)
    simp only [Set.mem_setOf_eq, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hb
    -- `G = ‖Δ‖² y¹² ≤ C² e^{−2c y} y¹²`
    have h1 : ‖Δf z‖ ^ 2 ≤ |C| ^ 2 * Real.exp (-c * z.im) ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb.trans (mul_le_mul_of_nonneg_right (le_abs_self _)
        (Real.exp_pos _).le)) 2
    -- `y¹² e^{−c₁ y} ≤ 12!/c₁¹²`
    have h2 : z.im ^ 12 * Real.exp (-c₁ * z.im) ≤ (Nat.factorial 12 : ℝ) / c₁ ^ 12 := by
      have := Real.pow_div_factorial_le_exp (x := c₁ * z.im) (by positivity) 12
      rw [mul_pow] at this
      have he : Real.exp (-c₁ * z.im) * Real.exp (c₁ * z.im) = 1 := by
        rw [← Real.exp_add]; simp
      rw [le_div_iff₀ (by positivity)]
      calc z.im ^ 12 * Real.exp (-c₁ * z.im) * c₁ ^ 12
          = (c₁ ^ 12 * z.im ^ 12 / (Nat.factorial 12 : ℝ)) * Real.exp (-c₁ * z.im) *
              (Nat.factorial 12 : ℝ) := by field_simp
        _ ≤ Real.exp (c₁ * z.im) * Real.exp (-c₁ * z.im) * (Nat.factorial 12 : ℝ) := by gcongr
        _ = (Nat.factorial 12 : ℝ) := by rw [mul_comm (Real.exp _), he, one_mul]
    have hexp : Real.exp (-c * z.im) ^ 2 = Real.exp (-c₁ * z.im) * Real.exp (-c₁ * z.im) *
        Real.exp (-c * z.im) := by
      rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; rw [hc₁]; ring
    unfold G
    calc ‖Δf z‖ ^ 2 * z.im ^ 12 ≤ |C| ^ 2 * Real.exp (-c * z.im) ^ 2 * z.im ^ 12 := by gcongr
      _ = |C| ^ 2 * (z.im ^ 12 * Real.exp (-c₁ * z.im)) * Real.exp (-c₁ * z.im) *
          Real.exp (-c * z.im) := by rw [hexp]; ring
      _ ≤ |C| ^ 2 * ((Nat.factorial 12 : ℝ) / c₁ ^ 12) * Real.exp (-c₁ * z.im) * 1 := by
          gcongr
          · exact Real.exp_le_one_iff.2 (by nlinarith)
      _ ≤ _ := by
          have : 0 ≤ M * Real.exp (c₁ * A') * Real.exp (-c₁ * z.im) := by positivity
          rw [mul_one, add_mul, mul_div_assoc]; linarith
  · have he : 1 ≤ Real.exp (c₁ * A') * Real.exp (-c₁ * z.im) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
    have : G z ≤ M * (Real.exp (c₁ * A') * Real.exp (-c₁ * z.im)) := (hM z).trans (le_mul_of_one_le_right hM0 he)
    have h0 : 0 ≤ |C| ^ 2 * (Nat.factorial 12 : ℝ) / c₁ ^ 12 * Real.exp (-c₁ * z.im) := by positivity
    rw [add_mul]; nlinarith

/-- On `𝓕`, `Q(m,n) ≥ (m² + n²)/(2y)`. -/
lemma Qf_ge {x y : ℝ} (hy : 0 < y) (hx : |x| ≤ 1 / 2) (hxy : 1 ≤ x ^ 2 + y ^ 2) (p : ℤ × ℤ) :
    ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) / (2 * y) ≤ Qf x y p := by
  have hx2 : x ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs x, abs_nonneg x]
  set m : ℝ := (p.1 : ℝ)
  set n : ℝ := (p.2 : ℝ)
  have hmn : |m * n * x| ≤ |m * n| / 2 := by
    rw [abs_mul]; nlinarith [abs_nonneg (m * n)]
  have hab : 2 * |m * n| ≤ m ^ 2 + n ^ 2 := by
    rw [abs_mul]
    nlinarith [sq_abs m, sq_abs n, sq_nonneg (|m| - |n|)]
  have h3 := (abs_le.1 hmn).1
  have h5 : m ^ 2 ≤ m ^ 2 * (x ^ 2 + y ^ 2) := le_mul_of_one_le_right (sq_nonneg m) hxy
  have key : m ^ 2 + n ^ 2 ≤ 2 * ((n + m * x) ^ 2 + m ^ 2 * y ^ 2) := by
    have e : 2 * ((n + m * x) ^ 2 + m ^ 2 * y ^ 2) = 2 * n ^ 2 + 4 * (m * n * x) +
        2 * (m ^ 2 * (x ^ 2 + y ^ 2)) := by ring
    rw [e]; linarith
  unfold Qf
  rw [div_le_iff₀ (by positivity)]
  have e2 : ((n + m * x) ^ 2 / y + m ^ 2 * y) * (2 * y) = 2 * ((n + m * x) ^ 2 + m ^ 2 * y ^ 2) := by
    first | (field_simp; ring) | field_simp
  rw [e2]; exact key

lemma theta_pos_terms_summable (x : ℝ) {y t : ℝ} (hy : 0 < y) (ht : 0 < t) :
    Summable fun p : ℤ × ℤ => rexp (-π * t * Qf x y p) := summable_theta x hy ht

lemma theta_nonneg (x y t : ℝ) : 0 ≤ theta x y t := tsum_nonneg fun _ => (Real.exp_pos _).le

/-- `Θ_z(t) ≤ Θ_z(1)/t` for `0 < t ≤ 1` and `Θ_z(t) ≤ Θ_z(1)` for `t ≥ 1`. -/
lemma theta_antitone (x : ℝ) {y : ℝ} (hy : 0 < y) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    theta x y t ≤ theta x y s := by
  have hQ : ∀ p, 0 ≤ Qf x y p := fun p => by unfold Qf; positivity
  exact (summable_theta x hy (hs.trans_le hst)).tsum_le_tsum (fun p => Real.exp_le_exp.2 (by
    have h := mul_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.2 hst)) (hQ p)
    linarith)) (summable_theta x hy hs)

lemma theta_le_of_le_one (x : ℝ) {y t : ℝ} (hy : 0 < y) (ht : 0 < t) (ht1 : t ≤ 1) :
    theta x y t ≤ theta x y 1 / t := by
  have h := theta_inv x hy (t := 1 / t) (by positivity)
  rw [one_div_one_div] at h
  rw [h, le_div_iff₀ ht]
  have := theta_antitone x hy one_pos (show (1:ℝ) ≤ 1 / t by rw [le_div_iff₀ ht]; linarith)
  calc 1 / t * theta x y (1 / t) * t = theta x y (1 / t) := by field_simp
    _ ≤ theta x y 1 := this

/-- `Θ_z(1) ≤ 2y ϑ₀²` on `𝓕`. -/
lemma theta_one_le {x y : ℝ} (hy : 1 / 2 ≤ y) (hx : |x| ≤ 1 / 2) (hxy : 1 ≤ x ^ 2 + y ^ 2) :
    theta x y 1 ≤ 2 * y * (∑' k : ℤ, rexp (-π * (k : ℝ) ^ 2)) ^ 2 := by
  have hy0 : 0 < y := by linarith
  set a : ℝ := 1 / (2 * y) with ha
  have ha0 : 0 < a := by positivity
  have hS := summable_gauss0 ha0
  have hprod : Summable fun p : ℤ × ℤ => rexp (-π * a * ((p.1 : ℝ) + 0) ^ 2) *
      rexp (-π * a * ((p.2 : ℝ) + 0) ^ 2) :=
    summable_mul_of_summable_norm (f := fun m : ℤ => rexp (-π * a * ((m : ℝ) + 0) ^ 2))
      (g := fun m : ℤ => rexp (-π * a * ((m : ℝ) + 0) ^ 2))
      (by simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hS)
      (by simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hS)
  have h1 : theta x y 1 ≤ ∑' p : ℤ × ℤ, rexp (-π * a * ((p.1 : ℝ) + 0) ^ 2) *
      rexp (-π * a * ((p.2 : ℝ) + 0) ^ 2) := by
    refine (summable_theta x hy0 one_pos).tsum_le_tsum (fun p => ?_) hprod
    rw [← Real.exp_add, Real.exp_le_exp]
    have hQ := Qf_ge hy0 hx hxy p
    have e : -π * a * ((p.1 : ℝ) + 0) ^ 2 + -π * a * ((p.2 : ℝ) + 0) ^ 2 =
        -π * (((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) / (2 * y)) := by rw [ha]; ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hQ Real.pi_pos.le
    linarith
  have hm := tsum_mul_tsum_of_summable_norm (f := fun m : ℤ => rexp (-π * a * ((m : ℝ) + 0) ^ 2))
    (g := fun m : ℤ => rexp (-π * a * ((m : ℝ) + 0) ^ 2))
    (by simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hS)
    (by simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hS)
  simp only at hm
  rw [← hm] at h1
  -- `∑ e^{−π a n²} ≤ (2y)^{1/2} ϑ₀`
  have h2 : ∑' n : ℤ, rexp (-π * a * ((n : ℝ) + 0) ^ 2) ≤
      (2 * y) ^ (1 / 2 : ℝ) * ∑' k : ℤ, rexp (-π * (k : ℝ) ^ 2) := by
    refine (tsum_gauss_le ha0 0).trans ?_
    have hpow : a ^ (-(1 / 2 : ℝ)) = (2 * y) ^ (1 / 2 : ℝ) := by
      rw [ha, Real.rpow_neg (by positivity), one_div, Real.inv_rpow (by positivity), inv_inv]
    rw [hpow]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hs1 : Summable fun k : ℤ => rexp (-π * (k : ℝ) ^ 2 / a) :=
      (summable_gauss (a := 1 / a) (by positivity) 0).congr fun k => by
        congr 1; rw [add_zero]; field_simp
    have hs2 : Summable fun k : ℤ => rexp (-π * (k : ℝ) ^ 2) :=
      (summable_gauss (a := 1) one_pos 0).congr fun k => by simp
    refine hs1.tsum_le_tsum (fun k => Real.exp_le_exp.2 ?_) hs2
    have hk : (0:ℝ) ≤ (k : ℝ) ^ 2 := sq_nonneg _
    have h2y : 1 ≤ 2 * y := by linarith
    have e : -π * (k : ℝ) ^ 2 / a = -π * (k : ℝ) ^ 2 * (2 * y) := by rw [ha]; field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_left h2y (mul_nonneg Real.pi_pos.le hk)
    nlinarith
  have h0 : 0 ≤ ∑' n : ℤ, rexp (-π * a * ((n : ℝ) + 0) ^ 2) := tsum_nonneg fun _ => (Real.exp_pos _).le
  have hsq : ((2 * y) ^ (1 / 2 : ℝ)) ^ 2 = 2 * y := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  calc theta x y 1 ≤ (∑' n : ℤ, rexp (-π * a * ((n : ℝ) + 0) ^ 2)) ^ 2 := by rw [sq]; exact h1
    _ ≤ ((2 * y) ^ (1 / 2 : ℝ) * ∑' k : ℤ, rexp (-π * (k : ℝ) ^ 2)) ^ 2 := by gcongr
    _ = 2 * y * (∑' k : ℤ, rexp (-π * (k : ℝ) ^ 2)) ^ 2 := by rw [mul_pow, hsq]

/-- `Θ_z(t) − 1 ≤ e^{−π(t−1)/(2y)} Θ_z(1)` on `𝓕`, `t ≥ 1`. -/
lemma theta_sub_one_le {x y : ℝ} (hy : 0 < y) (hx : |x| ≤ 1 / 2) (hxy : 1 ≤ x ^ 2 + y ^ 2) {t : ℝ}
    (ht : 1 ≤ t) : theta x y t - 1 ≤ rexp (-π * (t - 1) / (2 * y)) * theta x y 1 := by
  have ht0 : 0 < t := by linarith
  have hsum := summable_theta x hy ht0
  set f : ℤ × ℤ → ℝ := fun p => rexp (-π * t * Qf x y p) with hf
  set f1 : ℤ × ℤ → ℝ := fun p => rexp (-π * 1 * Qf x y p) with hf1
  have h00 : f (0, 0) = 1 := by simp [hf, Qf]
  have hite : Summable fun p : ℤ × ℤ => if p = (0, 0) then (0:ℝ) else f p :=
    hsum.of_nonneg_of_le (fun p => by split_ifs <;> simp [hf, (Real.exp_pos _).le])
      (fun p => by split_ifs <;> simp [hf, (Real.exp_pos _).le])
  have h0 : theta x y t - 1 = ∑' p : ℤ × ℤ, if p = (0, 0) then (0:ℝ) else f p := by
    unfold theta
    rw [hsum.tsum_eq_add_tsum_ite (0, 0), h00, add_sub_cancel_left]
  rw [h0]
  unfold theta
  rw [← tsum_mul_left]
  refine hite.tsum_le_tsum (fun p => ?_) ((summable_theta x hy one_pos).mul_left _)
  by_cases hp : p = (0, 0)
  · subst hp; simp only [if_true]; positivity
  · rw [if_neg hp, hf, ← Real.exp_add, Real.exp_le_exp]
    have hQ := Qf_ge hy hx hxy p
    have hmn : (1:ℝ) ≤ (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by
      have : p.1 ≠ 0 ∨ p.2 ≠ 0 := by
        by_contra h; push Not at h; exact hp (Prod.ext h.1 h.2)
      rcases this with h | h
      · have : (1:ℝ) ≤ (p.1 : ℝ) ^ 2 := by
          have := Int.one_le_abs h
          have : (1:ℝ) ≤ |(p.1 : ℝ)| := by exact_mod_cast this
          nlinarith [sq_abs (p.1 : ℝ)]
        nlinarith [sq_nonneg (p.2 : ℝ)]
      · have : (1:ℝ) ≤ (p.2 : ℝ) ^ 2 := by
          have := Int.one_le_abs h
          have : (1:ℝ) ≤ |(p.2 : ℝ)| := by exact_mod_cast this
          nlinarith [sq_abs (p.2 : ℝ)]
        nlinarith [sq_nonneg (p.1 : ℝ)]
    have hQ1 : 1 / (2 * y) ≤ Qf x y p :=
      le_trans (div_le_div_of_nonneg_right hmn (by positivity)) hQ
    have : (t - 1) * (1 / (2 * y)) ≤ (t - 1) * Qf x y p :=
      mul_le_mul_of_nonneg_left hQ1 (by linarith)
    have hπ := Real.pi_pos
    have e : -π * (t - 1) / (2 * y) = -π * ((t - 1) * (1 / (2 * y))) := by ring
    rw [e]
    nlinarith

end RamanujanTau.RankinError
