/-
# Real quantities of the tail argument for a fixed `U₀ = U(n)`, and their closed forms

`δ = √(−f''(0)/2)`, `A = f'(0)`, `φ`, `Φ_m = φ^{(m)}/δ^m`. The closed forms in the variables
`t₀ = U₀^{-1/2}`, `ρ = U(s)/U₀`, `c₂ = −Q₂(0)/2` are exactly what `boxI` evaluates in intervals.
-/
import RamanujanTau.JensenThreshold.Tail.IvLemmas

set_option autoImplicit false

namespace JensenThreshold.Tail

open Real Finset

variable (U0 : ℝ)

noncomputable def t0v : ℝ := (Real.sqrt U0)⁻¹
noncomputable def Qv (m : ℕ) (s : ℝ) : ℝ := evalQZ (Qd m) (Us U0 s)⁻¹ (Us U0 s / (Us U0 s - 1))
noncomputable def c2v : ℝ := -Qv U0 2 0 / 2
noncomputable def δv : ℝ := Real.sqrt (-fch U0 2 0 / 2)
noncomputable def Av : ℝ := fch U0 1 0
noncomputable def φv (i : ℕ) (s : ℝ) : ℝ :=
  if i = 0 then fch U0 0 s - fch U0 0 0 - Av U0 * s else if i = 1 then fch U0 1 s - Av U0 else fch U0 i s
noncomputable def Φv (i : ℕ) (s : ℝ) : ℝ := φv U0 i s / δv U0 ^ i
/-- `√c₂`-power: `c₂^{m/2}` written with integer exponents. -/
noncomputable def c2p (m : ℕ) : ℝ := c2v U0 ^ (m / 2) * (if m % 2 = 1 then Real.sqrt (c2v U0) else 1)

variable {U0}

lemma Us_zero (hU0 : 1 < U0) : Us U0 0 = U0 := by
  simp [Us, Real.sqrt_sq (by linarith : (0 : ℝ) ≤ U0)]

lemma t0v_pos (hU0 : 1 < U0) : 0 < t0v U0 := by
  unfold t0v; have : 0 < Real.sqrt U0 := Real.sqrt_pos.mpr (by linarith); positivity

lemma t0v_sq (hU0 : 1 < U0) : t0v U0 ^ 2 = U0⁻¹ := by
  unfold t0v; rw [inv_pow, Real.sq_sqrt (by linarith)]

lemma fch_eq_Q (hU0 : 1 < U0) {m : ℕ} (hm : 1 ≤ m) (hq : okQ m (Pz m) = true) {s : ℝ} (hs : 0 ≤ s) :
    fch U0 m s = (aC / 2) ^ m * ((Us U0 s)⁻¹) ^ (2 * m - 1) * Qv U0 m s := by
  have hU := one_lt_Us hU0 hs
  simp only [fch, if_neg (show m ≠ 0 by omega)]
  rw [evalZ_eq_Q m (Pz m) hq hU, Qv, Qd]; ring

lemma f2_zero_eq (hU0 : 1 < U0) (hq : okQ 2 (Pz 2) = true) :
    fch U0 2 0 = -2 * (aC / 2) ^ 2 * (t0v U0 ^ 3) ^ 2 * c2v U0 := by
  rw [fch_eq_Q hU0 (by norm_num) hq le_rfl, Us_zero hU0, c2v]
  have : (t0v U0 ^ 3) ^ 2 = (U0⁻¹) ^ 3 := by rw [← pow_mul, show 3 * 2 = 2 * 3 by rfl, pow_mul, t0v_sq hU0]
  rw [this]; norm_num
  try ring

lemma δv_eq (hU0 : 1 < U0) (hq : okQ 2 (Pz 2) = true) (hc : 0 ≤ c2v U0) :
    δv U0 = aC / 2 * t0v U0 ^ 3 * Real.sqrt (c2v U0) := by
  unfold δv
  rw [f2_zero_eq hU0 hq]
  have ht := t0v_pos hU0
  have ha := aC_pos
  rw [show -(-2 * (aC / 2) ^ 2 * (t0v U0 ^ 3) ^ 2 * c2v U0) / 2 = (aC / 2 * t0v U0 ^ 3) ^ 2 * c2v U0 by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

lemma δv_pos (hU0 : 1 < U0) (hq : okQ 2 (Pz 2) = true) (hc : 0 < c2v U0) : 0 < δv U0 := by
  rw [δv_eq hU0 hq hc.le]
  have := t0v_pos hU0; have := aC_pos; have := Real.sqrt_pos.mpr hc; positivity

lemma sqrt_pow_eq (c : ℝ) (hc : 0 ≤ c) (m : ℕ) :
    Real.sqrt c ^ m = c ^ (m / 2) * (if m % 2 = 1 then Real.sqrt c else 1) := by
  have h2 : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc
  conv_lhs => rw [← Nat.div_add_mod m 2, pow_add, pow_mul, h2]
  rcases Nat.mod_two_eq_zero_or_one m with h | h <;> simp [h]

lemma δv_pow (hU0 : 1 < U0) (hq : okQ 2 (Pz 2) = true) (hc : 0 ≤ c2v U0) (m : ℕ) :
    δv U0 ^ m = (aC / 2) ^ m * t0v U0 ^ (3 * m) * c2p U0 m := by
  rw [δv_eq hU0 hq hc, mul_pow, mul_pow, ← pow_mul, c2p, sqrt_pow_eq _ hc, mul_comm 3 m]

/-! ## the chain `φ` -/

lemma φv_chain (hU0 : 1 < U0) (i : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivAt (φv U0 i) (φv U0 (i + 1) s) s := by
  rcases i with _ | _ | i
  · have h := ((fch_hasDerivAt hU0 0 hs).sub_const (fch U0 0 0)).sub ((hasDerivAt_id s).const_mul (Av U0))
    have e : φv U0 0 = fun s => fch U0 0 s - fch U0 0 0 - Av U0 * s := by funext s; simp [φv]
    rw [e]; convert h using 1 <;> simp [φv]
  · have h := (fch_hasDerivAt hU0 1 hs).sub_const (Av U0)
    have e : φv U0 1 = fun s => fch U0 1 s - Av U0 := by funext s; simp [φv]
    rw [e]; convert h using 1 <;> simp [φv]
  · have h := fch_hasDerivAt hU0 (i + 2) hs
    have e : φv U0 (i + 2) = fch U0 (i + 2) := by funext s; simp [φv]
    rw [e]; convert h using 1 <;> simp [φv]

lemma φv_ge2 {i : ℕ} (hi : 2 ≤ i) (s : ℝ) : φv U0 i s = fch U0 i s := by
  simp [φv, show i ≠ 0 by omega, show i ≠ 1 by omega]

lemma φv0_zero : φv U0 0 0 = 0 := by simp [φv]
lemma φv1_zero : φv U0 1 0 = 0 := by simp [φv, Av]

/-! ## closed forms of `Φ` -/

lemma Φv_zero_ge2 (hU0 : 1 < U0) (hq2 : okQ 2 (Pz 2) = true) (hc : 0 < c2v U0) {m : ℕ} (hm : 2 ≤ m)
    (hq : okQ m (Pz m) = true) :
    Φv U0 m 0 = Qv U0 m 0 * t0v U0 ^ (m - 2) * (c2p U0 m)⁻¹ := by
  unfold Φv
  rw [φv_ge2 hm, fch_eq_Q hU0 (by omega) hq le_rfl, Us_zero hU0, δv_pow hU0 hq2 hc.le]
  have ht := t0v_pos hU0
  have ha := aC_pos
  have hcp : 0 < c2p U0 m := by
    unfold c2p; have := Real.sqrt_pos.mpr hc; split_ifs <;> positivity
  have hU : U0⁻¹ = t0v U0 ^ 2 := (t0v_sq hU0).symm
  rw [hU, ← pow_mul]
  have : t0v U0 ^ (2 * (2 * m - 1)) = t0v U0 ^ (3 * m) * t0v U0 ^ (m - 2) := by
    rw [← pow_add]; congr 1; omega
  rw [this]; field_simp

lemma Φv2_zero (hU0 : 1 < U0) (hq2 : okQ 2 (Pz 2) = true) (hc : 0 < c2v U0) : Φv U0 2 0 = -2 := by
  unfold Φv
  rw [φv_ge2 le_rfl]
  have hd := δv_pos hU0 hq2 hc
  have hsq : δv U0 ^ 2 = -fch U0 2 0 / 2 := by
    unfold δv
    rw [Real.sq_sqrt]
    rw [f2_zero_eq hU0 hq2]; have := aC_pos; have := t0v_pos hU0; nlinarith [sq_nonneg (aC / 2 * t0v U0 ^ 3)]
  have hne : fch U0 2 0 ≠ 0 := by
    intro h; rw [h] at hsq; simp at hsq; exact hd.ne' hsq
  rw [hsq]; field_simp

lemma Φv_ge2 (hU0 : 1 < U0) (hq2 : okQ 2 (Pz 2) = true) (hc : 0 < c2v U0) {m : ℕ} (hm : 2 ≤ m)
    (hq : okQ m (Pz m) = true) {s : ℝ} (hs : 0 ≤ s) :
    Φv U0 m s = (U0 / Us U0 s) ^ (2 * m - 1) * t0v U0 ^ (m - 2) * Qv U0 m s * (c2p U0 m)⁻¹ := by
  unfold Φv
  rw [φv_ge2 hm, fch_eq_Q hU0 (by omega) hq hs, δv_pow hU0 hq2 hc.le]
  have ht := t0v_pos hU0
  have ha := aC_pos
  have hUs := one_lt_Us hU0 hs
  have hUs0 : Us U0 s ≠ 0 := by linarith
  have hcp : 0 < c2p U0 m := by
    unfold c2p; have := Real.sqrt_pos.mpr hc; split_ifs <;> positivity
  have e1 : (Us U0 s)⁻¹ = U0 / Us U0 s * t0v U0 ^ 2 := by
    rw [t0v_sq hU0]; field_simp
  rw [e1, mul_pow, ← pow_mul]
  have : t0v U0 ^ (2 * (2 * m - 1)) = t0v U0 ^ (3 * m) * t0v U0 ^ (m - 2) := by
    rw [← pow_add]; congr 1; omega
  rw [this]; field_simp

/-- `f''(θ)/δ` in closed form. -/
lemma f2_div_δ (hU0 : 1 < U0) (hq2 : okQ 2 (Pz 2) = true) (hc : 0 < c2v U0) {s : ℝ} (hs : 0 ≤ s) :
    fch U0 2 s / δv U0 = aC / 2 * (U0 / Us U0 s) ^ 3 * t0v U0 ^ 3 * Qv U0 2 s * (Real.sqrt (c2v U0))⁻¹ := by
  rw [fch_eq_Q hU0 (by norm_num) hq2 hs, δv_eq hU0 hq2 hc.le]
  have ht := t0v_pos hU0
  have ha := aC_pos
  have hUs := one_lt_Us hU0 hs
  have hsq := Real.sqrt_pos.mpr hc
  have hUs0 : Us U0 s ≠ 0 := by linarith
  have e1 : (Us U0 s)⁻¹ = U0 / Us U0 s * t0v U0 ^ 2 := by rw [t0v_sq hU0]; field_simp
  rw [show 2 * 2 - 1 = 3 by norm_num, e1, div_pow, mul_pow, div_pow]
  field_simp

lemma f2_eq (hU0 : 1 < U0) (hq2 : okQ 2 (Pz 2) = true) {s : ℝ} (hs : 0 ≤ s) :
    fch U0 2 s = (aC / 2) ^ 2 * ((Us U0 s)⁻¹) ^ 3 * Qv U0 2 s := fch_eq_Q hU0 (by norm_num) hq2 hs

/-! ## Taylor consequences for `φ₀`, `φ₁` -/

lemma φv0_bounds (hU0 : 1 < U0) {X lo hi : ℝ} (hb : ∀ t, 0 ≤ t → t ≤ X → lo ≤ fch U0 2 t ∧ fch U0 2 t ≤ hi)
    {s : ℝ} (hs : 0 ≤ s) (hsX : s ≤ X) : lo * s ^ 2 / 2 ≤ φv U0 0 s ∧ φv U0 0 s ≤ hi * s ^ 2 / 2 := by
  have := taylor_bounds (fch U0) 2 (fun i _ t ht => fch_hasDerivAt hU0 i ht) hb hs hsX
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, Nat.factorial,
    Nat.cast_one, div_one, mul_one, zero_add] at this
  have e : φv U0 0 s = fch U0 0 s - (fch U0 0 0 + fch U0 1 0 * s) := by simp [φv, Av]; ring
  rw [e]; norm_num at this ⊢; exact this

lemma φv1_bounds (hU0 : 1 < U0) {X lo hi : ℝ} (hb : ∀ t, 0 ≤ t → t ≤ X → lo ≤ fch U0 2 t ∧ fch U0 2 t ≤ hi)
    {s : ℝ} (hs : 0 ≤ s) (hsX : s ≤ X) : lo * s ≤ φv U0 1 s ∧ φv U0 1 s ≤ hi * s := by
  have := taylor_bounds (fun i => fch U0 (i + 1)) 1 (fun i _ t ht => fch_hasDerivAt hU0 (i + 1) ht)
    (lo := lo) (hi := hi) (X := X) (fun t h1 h2 => hb t h1 h2) hs hsX
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, Nat.factorial,
    Nat.cast_one, div_one, mul_one, zero_add] at this
  have e : φv U0 1 s = fch U0 1 s - fch U0 1 0 := by simp [φv, Av]
  rw [e]; exact this

end JensenThreshold.Tail
