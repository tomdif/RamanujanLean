/-
# Per-prime structure: normalized Hecke eigenvalues, Satake parameters, local factors

For a prime `p` put `r = p^{−11/2}`, `u_k = τ(p^k) r^k` (so `u_k² = τ(p^k)²/p^{11k}`) and
`λ = u_1`.  The Hecke recurrence gives `u_{k+2} = λu_{k+1} − u_k`.  We pick `α, β ∈ ℂ` with
`α + β = λ`, `αβ = 1`, `‖β‖ ≤ 1 ≤ ‖α‖`, and prove **without Deligne** that `‖α‖² ≤ p`, using only
Rankin's linear bound `τ(n)²/n¹¹ ≤ K n` (`α^{k+1} = u_{k+1} − βu_k`).

Local factors:
* `tau_local`: `1 − τ(p)p^{−s} + p^{11}p^{−2s} = (1 − αZ)(1 − βZ)`, `Z = p^{−(s−11/2)}`;
* `rs_local`: `(1 − p^{−2s})⁻¹ ∑_e τ(p^e)²p^{−11e}p^{−es} = ((1−Y)²(1−α²Y)(1−β²Y))⁻¹`, `Y = p^{−s}`.
-/
import RamanujanTau.EdgeNonvanishing.RS
import RamanujanTau.HeckeZeros.EulerProduct

set_option autoImplicit false

namespace RamanujanTau.EdgeNonvanishing

open Complex Finset Filter LSeries

/-- `r = p^{−11/2}`. -/
noncomputable def rr (p : ℕ) : ℝ := (p : ℝ) ^ (-(11 / 2 : ℝ))

/-- `u_k = τ(p^k) p^{−11k/2}`. -/
noncomputable def uu (p k : ℕ) : ℝ := (tau (p ^ k) : ℝ) * rr p ^ k

/-- The normalized eigenvalue `λ(p) = τ(p)/p^{11/2}`. -/
noncomputable def lam (p : ℕ) : ℝ := uu p 1

lemma rr_sq {p : ℕ} (hp : p.Prime) : (p : ℝ) ^ 11 * rr p ^ 2 = 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  unfold rr
  rw [← Real.rpow_natCast ((p : ℝ) ^ _) 2, ← Real.rpow_mul hp0.le, ← Real.rpow_natCast (p : ℝ) 11,
    ← Real.rpow_add hp0]
  norm_num

lemma uu_zero (p : ℕ) : uu p 0 = 1 := by simp [uu, tau_one]

lemma uu_rec {p : ℕ} (hp : p.Prime) (k : ℕ) : uu p (k + 2) = lam p * uu p (k + 1) - uu p k := by
  have h := tau_hecke_recurrence hp (r := k + 1) (by omega)
  have hr := rr_sq hp
  simp only [lam, uu, pow_one]
  rw [show k + 2 = k + 1 + 1 by ring, h, show k + 1 - 1 = k by omega]
  push_cast
  linear_combination (-(tau (p ^ k) : ℝ) * rr p ^ k) * hr

lemma rsb_pow {p : ℕ} (hp : p.Prime) (k : ℕ) : rsb (p ^ k) = uu p k ^ 2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hr := rr_sq hp
  have hrk : ((p : ℝ) ^ k) ^ 11 * (rr p ^ k) ^ 2 = 1 := by
    rw [← pow_mul, ← pow_mul, mul_comm k 11, mul_comm k 2, pow_mul, pow_mul, ← mul_pow, hr, one_pow]
  unfold rsb uu
  push_cast
  have hne : ((p : ℝ) ^ k) ^ 11 ≠ 0 := by positivity
  field_simp
  linear_combination (-(tau (p ^ k) : ℝ) ^ 2) * hrk

/-- Satake parameters: `α + β = λ`, `αβ = 1`, `‖β‖ ≤ 1 ≤ ‖α‖`. -/
lemma satake (l : ℝ) : ∃ α β : ℂ, α * β = 1 ∧ α + β = l ∧ 1 ≤ ‖α‖ ∧ ‖β‖ ≤ 1 := by
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq ((l : ℂ) ^ 2 - 4) (n := 2) (by norm_num)
  set a1 : ℂ := (l + d) / 2
  set a2 : ℂ := (l - d) / 2
  have h12 : a1 * a2 = 1 := by simp only [a1, a2]; linear_combination (-1 / 4 : ℂ) * hd
  have hs : a1 + a2 = l := by simp only [a1, a2]; ring
  have hn : ‖a1‖ * ‖a2‖ = 1 := by rw [← norm_mul, h12, norm_one]
  rcases le_or_gt 1 ‖a1‖ with h | h
  · exact ⟨a1, a2, h12, hs, h, by nlinarith [norm_nonneg a2]⟩
  · refine ⟨a2, a1, by rw [mul_comm]; exact h12, by rw [add_comm]; exact hs, ?_, h.le⟩
    nlinarith [norm_nonneg a2, norm_nonneg a1]

/-- **`‖α‖² ≤ p` without Deligne.** -/
theorem alpha_sq_le {p : ℕ} (hp : p.Prime) {α β : ℂ} (hab : α * β = 1) (hs : α + β = lam p)
    (hβ : ‖β‖ ≤ 1) : ‖α‖ ^ 2 ≤ p := by
  obtain ⟨K, hK0, hK⟩ := rs_le_linear
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp0 : (0 : ℝ) < p := by linarith
  have key : ∀ k, (uu p (k + 1) : ℂ) - β * uu p k = α ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
      simp only [uu_zero, zero_add, pow_one]; push_cast
      have : (uu p 1 : ℂ) = lam p := rfl
      rw [this, ← hs]; ring
    | succ k ih =>
      rw [show k + 1 + 1 = k + 2 by ring, uu_rec hp, pow_succ, ← ih]
      push_cast
      rw [← hs]
      linear_combination (uu p k : ℂ) * hab
  have hu : ∀ k, uu p k ^ 2 ≤ K * (p : ℝ) ^ k := by
    intro k
    rw [← rsb_pow hp k]
    have := hK (p ^ k); push_cast at this; exact this
  have hbd : ∀ k, (‖α‖ ^ 2 / p) ^ (k + 1) ≤ 4 * K := by
    intro k
    have h1 : ‖α‖ ^ (k + 1) ≤ |uu p (k + 1)| + |uu p k| := by
      rw [← norm_pow, ← key]
      calc ‖(uu p (k + 1) : ℂ) - β * uu p k‖ ≤ ‖(uu p (k + 1) : ℂ)‖ + ‖β * uu p k‖ := norm_sub_le _ _
        _ ≤ |uu p (k + 1)| + |uu p k| := by
          rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
          gcongr
          nlinarith [abs_nonneg (uu p k)]
    have h2 : (‖α‖ ^ (k + 1)) ^ 2 ≤ 2 * (uu p (k + 1) ^ 2 + uu p k ^ 2) := by
      have := pow_le_pow_left₀ (by positivity) h1 2
      nlinarith [sq_abs (uu p (k + 1)), sq_abs (uu p k), sq_nonneg (|uu p (k + 1)| - |uu p k|)]
    have h3 : (p : ℝ) ^ k ≤ (p : ℝ) ^ (k + 1) := pow_le_pow_right₀ hp1 (by omega)
    have h4 := hu (k + 1)
    have h5 := hu k
    have hpk : 0 < (p : ℝ) ^ (k + 1) := by positivity
    rw [div_pow, div_le_iff₀ hpk, ← pow_mul, mul_comm 2 (k + 1), pow_mul]
    nlinarith
  by_contra hcon
  push_neg at hcon
  have hq : 1 < ‖α‖ ^ 2 / p := by rw [lt_div_iff₀ hp0]; linarith
  obtain ⟨n, hn1, hn2⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hq).eventually_gt_atTop (4 * K)).and
    (eventually_ge_atTop 1) |>.exists
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  linarith [hbd k]

/-- The local polynomial of `L(Δ,s)` factors over the Satake parameters. -/
theorem tau_local (s : ℂ) {p : ℕ} (hp : p.Prime) {α β : ℂ} (hab : α * β = 1)
    (hs : α + β = lam p) :
    HeckeZeros.localPoly s p = (1 - α * (p : ℂ) ^ (-(s - 11 / 2))) * (1 - β * (p : ℂ) ^ (-(s - 11 / 2))) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  set Z := (p : ℂ) ^ (-(s - 11 / 2))
  have hw : (p : ℂ) ^ (-(11 / 2 : ℂ)) = ((rr p : ℝ) : ℂ) := by
    rw [rr, Complex.ofReal_cpow (by positivity)]; push_cast; rfl
  have hsplit : (p : ℂ) ^ (-s) = ((rr p : ℝ) : ℂ) * Z := by
    rw [← hw, ← cpow_add _ _ hp0]; congr 1; ring
  have hr : ((p : ℂ)) ^ 11 * ((rr p : ℝ) : ℂ) ^ 2 = 1 := by exact_mod_cast rr_sq hp
  have hl : ((lam p : ℝ) : ℂ) = tauC p * ((rr p : ℝ) : ℂ) := by
    simp [lam, uu, tauC]
  rw [HeckeZeros.localPoly, hsplit]
  rw [← hs] at hl
  linear_combination Z * hl + (Z ^ 2) * hr - Z ^ 2 * hab

lemma term_rs_pow (s : ℂ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    term rsB s (p ^ e) = ((uu p e ^ 2 : ℝ) : ℂ) * ((p : ℂ) ^ (-s)) ^ e := by
  rw [term_of_ne_zero (pow_ne_zero _ hp.ne_zero), Nat.cast_pow, ← natCast_cpow_natCast_mul,
    mul_comm (e : ℂ), cpow_mul_nat, div_eq_mul_inv, ← inv_pow, ← cpow_neg, rsB, rsb_pow hp]

/-- The `ζ(2s) R(s)` local factor. -/
theorem rs_local {s : ℂ} (hs : 1 < s.re) {p : ℕ} (hp : p.Prime) {α β : ℂ} (hab : α * β = 1)
    (hsum : α + β = lam p) (hα : ‖α‖ ^ 2 ≤ p) (hβ : ‖β‖ ≤ 1) :
    (1 - (p : ℂ) ^ (-(2 * s)))⁻¹ * ∑' e, term rsB s (p ^ e) =
      ((1 - (p : ℂ) ^ (-s)) ^ 2 * (1 - α ^ 2 * (p : ℂ) ^ (-s)) * (1 - β ^ 2 * (p : ℂ) ^ (-s)))⁻¹ := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  set Y := (p : ℂ) ^ (-s)
  have hY : ‖Y‖ * p < 1 := by
    rw [norm_natCast_cpow_of_pos hp.pos, neg_re]
    have : (p : ℝ) ^ (-s.re) * p = (p : ℝ) ^ (1 - s.re) := by
      rw [Real.rpow_sub (by positivity), Real.rpow_one, Real.rpow_neg (by positivity)]; field_simp
    rw [this]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hY1 : ‖Y‖ < 1 := by nlinarith [norm_nonneg Y]
  have hαY : ‖α ^ 2 * Y‖ < 1 := by
    rw [norm_mul, norm_pow]; nlinarith [norm_nonneg Y]
  have hβY : ‖β ^ 2 * Y‖ < 1 := by
    rw [norm_mul, norm_pow]
    have : ‖β‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg β]
    nlinarith [norm_nonneg Y]
  have ne1 : ∀ z : ℂ, ‖z‖ < 1 → 1 - z ≠ 0 := fun z hz h => by
    have : z = 1 := by linear_combination -h
    rw [this, norm_one] at hz; exact lt_irrefl _ hz
  have hY2 : (p : ℂ) ^ (-(2 * s)) = Y ^ 2 := by
    rw [show -(2 * s) = (2 : ℕ) * (-s) by push_cast; ring, cpow_nat_mul]
  -- the series
  set v : ℕ → ℂ := fun k => ((uu p k ^ 2 : ℝ) : ℂ)
  set g : ℕ → ℂ := fun k => v k * Y ^ k
  have hsumg : Summable g := by
    have hinj : Function.Injective (fun e : ℕ => p ^ e) := Nat.pow_right_injective hp.two_le
    have := (rs_summable hs).comp_injective hinj
    simpa [Function.comp_def, term_rs_pow s hp, g, v] using this
  have hT : ∑' e, term rsB s (p ^ e) = ∑' k, g k := by
    congr 1; funext e; exact term_rs_pow s hp e
  set c : ℂ := ((lam p : ℝ) : ℂ) ^ 2 - 1
  have hrec : ∀ k, g (k + 3) = c * Y * g (k + 2) - c * Y ^ 2 * g (k + 1) + Y ^ 3 * g k := by
    intro k
    have e2 := uu_rec hp k
    have e3 := uu_rec hp (k + 1)
    have hv : uu p (k + 3) ^ 2 = (lam p ^ 2 - 1) * uu p (k + 2) ^ 2 - (lam p ^ 2 - 1) * uu p (k + 1) ^ 2
        + uu p k ^ 2 := by
      rw [show k + 1 + 2 = k + 3 by ring] at e3
      rw [e3, e2]; ring
    simp only [g, v, c]
    rw [hv]; push_cast; ring
  set S := ∑' k, g k
  have g0 : g 0 = 1 := by simp [g, v, uu_zero]
  have g1 : g 1 = ((lam p : ℝ) : ℂ) ^ 2 * Y := by
    simp only [g, v, lam, pow_one]; push_cast; ring
  have g2 : g 2 = c ^ 2 * Y ^ 2 := by
    simp only [g, v, c]
    have := uu_rec hp 0
    simp only [uu_zero, zero_add] at this
    rw [this]
    have h1 : uu p 1 = lam p := rfl
    rw [h1]; push_cast; ring
  have hs1 : Summable fun k => g (k + 1) := (summable_nat_add_iff 1).mpr hsumg
  have hs2 : Summable fun k => g (k + 2) := (summable_nat_add_iff 2).mpr hsumg
  have hs3 : Summable fun k => g (k + 3) := (summable_nat_add_iff 3).mpr hsumg
  have e1 : S = g 0 + ∑' k, g (k + 1) := hsumg.tsum_eq_zero_add
  have e2 : ∑' k, g (k + 1) = g 1 + ∑' k, g (k + 2) := hs1.tsum_eq_zero_add
  have e3 : ∑' k, g (k + 2) = g 2 + ∑' k, g (k + 3) := hs2.tsum_eq_zero_add
  have e4 : ∑' k, g (k + 3) = c * Y * ∑' k, g (k + 2) - c * Y ^ 2 * ∑' k, g (k + 1) + Y ^ 3 * S := by
    simp_rw [hrec]
    rw [Summable.tsum_add, Summable.tsum_sub, tsum_mul_left, tsum_mul_left, tsum_mul_left]
    · exact hs2.mul_left _
    · exact hs1.mul_left _
    · exact (hs2.mul_left _).sub (hs1.mul_left _)
    · exact hsumg.mul_left _
  have hcub : S * (1 - c * Y + c * Y ^ 2 - Y ^ 3) = 1 + Y := by
    rw [g0] at e1; rw [g1] at e2; rw [g2] at e3
    have hl : ((lam p : ℝ) : ℂ) ^ 2 = c + 1 := by simp only [c]; ring
    linear_combination (1 - c * Y + c * Y ^ 2) * e1 + (1 - c * Y) * e2 + e3 + e4 + (Y - c * Y ^ 2) * hl
  have hfac : 1 - c * Y + c * Y ^ 2 - Y ^ 3 = (1 - Y) * (1 - α ^ 2 * Y) * (1 - β ^ 2 * Y) := by
    simp only [c]
    rw [← hsum]
    linear_combination (-2 * Y - (α * β - 1) * Y ^ 2 + (α * β + 1) * Y ^ 3) * hab
  have hA := ne1 _ hY1
  have hB := ne1 _ hαY
  have hC := ne1 _ hβY
  have hD : 1 + Y ≠ 0 := by
    have := ne1 (-Y) (by rwa [norm_neg]); rwa [sub_neg_eq_add] at this
  rw [hT, hY2]
  rw [hfac] at hcub
  have hS : S = (1 + Y) / ((1 - Y) * (1 - α ^ 2 * Y) * (1 - β ^ 2 * Y)) := by
    rw [eq_div_iff (by simp [hA, hB, hC])]; exact hcub
  rw [hS]
  have h1Y : 1 - Y ^ 2 = (1 - Y) * (1 + Y) := by ring
  rw [h1Y]
  field_simp

end RamanujanTau.EdgeNonvanishing
