/-
# The analytic model behind the Jensen tail

For `U₀ > 1` put `U(s) = √(U₀² + a s)` with `a = 2π²/3`. Then `uk 1 (n+j) = U(j)` when `U₀ = uk 1 n`.
Write `f(s) = F(U(s))`, where `F(U) = U + log(U−1) − 3 log U`, so that `Mmain (n+j) = (Kc/2)·e^{f(j)}`.

* `fch U₀ m` : the `m`-th derivative of `f`. For `m ≥ 1` it equals `(a/2)^m · E_m(U(s))`, where
  `E_m = evalZ (Pz m)` is an explicit integer combination of `U^{-p}(U−1)^{-q}`. **`fch_hasDerivAt`**.
* `toQ`/`evalQZ` : `E_m(U) = U^{-(2m−1)} · Q_m(1/U, U/(U−1))` (**`evalZ_eq_Q`**), the form used for interval
  evaluation.
-/
import RamanujanTau.JensenThreshold.Tail.Calculus
import RamanujanTau.JensenThreshold.Tail.Defs
import RamanujanTau.Rademacher.LogConcaveTail

set_option autoImplicit false

namespace JensenThreshold.Tail

open Real

noncomputable def aC : ℝ := 2 * π ^ 2 / 3

lemma aC_pos : 0 < aC := by unfold aC; have := pi_pos; positivity

noncomputable def Fn (U : ℝ) : ℝ := U + Real.log (U - 1) - 3 * Real.log U

noncomputable def Us (U0 s : ℝ) : ℝ := Real.sqrt (U0 ^ 2 + aC * s)

noncomputable def evalZ (P : UWZ) (U : ℝ) : ℝ :=
  (P.map fun m => (m.2.2 : ℝ) * (U⁻¹) ^ m.1 * ((U - 1)⁻¹) ^ m.2.1).sum

lemma evalZ_nil (U : ℝ) : evalZ [] U = 0 := by simp [evalZ]

lemma evalZ_cons (m : ℕ × ℕ × ℤ) (P : UWZ) (U : ℝ) :
    evalZ (m :: P) U = (m.2.2 : ℝ) * (U⁻¹) ^ m.1 * ((U - 1)⁻¹) ^ m.2.1 + evalZ P U := by
  simp [evalZ]

lemma evalZ_append (P Q : UWZ) (U : ℝ) : evalZ (P ++ Q) U = evalZ P U + evalZ Q U := by
  simp [evalZ, List.map_append, List.sum_append]

lemma evalZ_insZ (m : ℕ × ℕ × ℤ) (P : UWZ) (U : ℝ) : evalZ (insZ m P) U = evalZ [m] U + evalZ P U := by
  induction P with
  | nil => simp [insZ, evalZ]
  | cons x xs ih =>
    unfold insZ
    split_ifs with h
    · obtain ⟨h1, h2⟩ := h
      simp only [evalZ_cons, evalZ_nil, h1, h2]; push_cast; ring
    · simp only [evalZ_cons, evalZ_nil, ih]; ring

lemma evalZ_normZ (P : UWZ) (U : ℝ) : evalZ (normZ P) U = evalZ P U := by
  induction P with
  | nil => rfl
  | cons x xs ih =>
    show evalZ (insZ x (normZ xs)) U = _
    rw [evalZ_insZ, ih, evalZ_cons, evalZ_cons, evalZ_nil]; ring

/-! ## derivatives along `U(s)` -/

lemma Us_sq_pos {U0 s : ℝ} (hU0 : 1 < U0) (hs : 0 ≤ s) : 0 < U0 ^ 2 + aC * s := by
  have := aC_pos; nlinarith

lemma one_lt_Us {U0 s : ℝ} (hU0 : 1 < U0) (hs : 0 ≤ s) : 1 < Us U0 s := by
  unfold Us
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  apply Real.sqrt_lt_sqrt (by norm_num)
  have := aC_pos; nlinarith

lemma U0_le_Us {U0 s : ℝ} (hU0 : 1 < U0) (hs : 0 ≤ s) : U0 ≤ Us U0 s := by
  unfold Us
  rw [show U0 = Real.sqrt (U0 ^ 2) by rw [Real.sqrt_sq (by linarith)]]
  apply Real.sqrt_le_sqrt
  have := aC_pos; rw [Real.sq_sqrt (by positivity)]; nlinarith

lemma Us_sq {U0 s : ℝ} (hU0 : 1 < U0) (hs : 0 ≤ s) : Us U0 s ^ 2 = U0 ^ 2 + aC * s :=
  Real.sq_sqrt (Us_sq_pos hU0 hs).le

lemma hasDerivAt_Us {U0 s : ℝ} (hU0 : 1 < U0) (hs : 0 ≤ s) :
    HasDerivAt (Us U0) (aC / (2 * Us U0 s)) s := by
  have h : HasDerivAt (fun s => U0 ^ 2 + aC * s) aC s := by
    simpa using (hasDerivAt_id s).const_mul aC |>.const_add (U0 ^ 2)
  have := h.sqrt (Us_sq_pos hU0 hs).ne'
  simpa [Us] using this

lemma hasDerivAt_uinv {U0 s : ℝ} (hU0 : 1 < U0) (hs : 0 ≤ s) :
    HasDerivAt (fun s => (Us U0 s)⁻¹) (-(aC / 2) * ((Us U0 s)⁻¹) ^ 3) s := by
  have hU := one_lt_Us hU0 hs
  have := (hasDerivAt_Us hU0 hs).inv (by linarith)
  convert this using 1
  field_simp

lemma hasDerivAt_winv {U0 s : ℝ} (hU0 : 1 < U0) (hs : 0 ≤ s) :
    HasDerivAt (fun s => (Us U0 s - 1)⁻¹) (-(aC / 2) * (Us U0 s)⁻¹ * ((Us U0 s - 1)⁻¹) ^ 2) s := by
  have hU := one_lt_Us hU0 hs
  have := ((hasDerivAt_Us hU0 hs).sub_const 1).inv (by linarith)
  convert this using 1
  have : Us U0 s - 1 ≠ 0 := by linarith
  field_simp

lemma pow_pred_mul {x : ℝ} (p k : ℕ) : (p : ℝ) * x ^ (p - 1) * x ^ (k + 1) = p * x ^ (p + k) := by
  rcases p with _ | p
  · simp
  · rw [show p + 1 - 1 = p by omega, mul_assoc, ← pow_add]; congr 2; omega

lemma hasDerivAt_evalZ {U0 s : ℝ} (hU0 : 1 < U0) (hs : 0 ≤ s) (P : UWZ) :
    HasDerivAt (fun s => evalZ P (Us U0 s)) (aC / 2 * evalZ (dZ P) (Us U0 s)) s := by
  induction P with
  | nil => simpa [evalZ, dZ] using hasDerivAt_const s (0 : ℝ)
  | cons m P ih =>
    obtain ⟨p, q, c⟩ := m
    have hu := (hasDerivAt_uinv hU0 hs).pow p
    have hw := (hasDerivAt_winv hU0 hs).pow q
    have ht := ((hu.const_mul (c : ℝ)).mul hw)
    have hsum := ht.add ih
    have e : (fun s => evalZ ((p, q, c) :: P) (Us U0 s)) =
        fun s => (c : ℝ) * (Us U0 s)⁻¹ ^ p * (Us U0 s - 1)⁻¹ ^ q + evalZ P (Us U0 s) := by
      funext s; rw [evalZ_cons]
    rw [e]
    convert hsum using 1
    simp only [dZ, List.flatMap_cons, evalZ_append, evalZ_cons, evalZ_nil] at *
    have h1 := pow_pred_mul (x := (Us U0 s)⁻¹) p 2
    have h2 := pow_pred_mul (x := (Us U0 s - 1)⁻¹) q 1
    have ed : evalZ (List.flatMap (fun m => [(m.1 + 2, m.2.1, -(m.1 : ℤ) * m.2.2),
        (m.1 + 1, m.2.1 + 1, -(m.2.1 : ℤ) * m.2.2)]) P) (Us U0 s) = evalZ (dZ P) (Us U0 s) := rfl
    rw [ed]
    push_cast
    set u := (Us U0 s)⁻¹
    set w := (Us U0 s - 1)⁻¹
    have h1' : (p : ℝ) * u ^ (p - 1) * u ^ 3 = p * u ^ (p + 2) := h1
    have h2' : (q : ℝ) * w ^ (q - 1) * w ^ 2 = q * w ^ (q + 1) := h2
    simp only [Pi.pow_apply]
    linear_combination (aC / 2 * c * w ^ q) * h1' + (aC / 2 * c * u ^ (p + 1)) * h2'

noncomputable def fch (U0 : ℝ) (m : ℕ) (s : ℝ) : ℝ :=
  if m = 0 then Fn (Us U0 s) else (aC / 2) ^ m * evalZ (Pz m) (Us U0 s)

lemma evalZ_P1 (U : ℝ) : evalZ P1 U = U⁻¹ + U⁻¹ * (U - 1)⁻¹ - 3 * U⁻¹ ^ 2 := by
  simp [evalZ, P1]; ring

theorem fch_hasDerivAt {U0 : ℝ} (hU0 : 1 < U0) (m : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivAt (fch U0 m) (fch U0 (m + 1) s) s := by
  have hU := one_lt_Us hU0 hs
  rcases m with _ | m
  · -- f' = (a/(2U))(1 + 1/(U−1) − 3/U)
    have hUs := hasDerivAt_Us hU0 hs
    have h1 := (hUs.sub_const 1).log (by linarith)
    have h2 := hUs.log (by linarith)
    have h := (hUs.add h1).sub (h2.const_mul 3)
    have e : fch U0 0 = fun s => Us U0 s + Real.log (Us U0 s - 1) - 3 * Real.log (Us U0 s) := by
      funext s; simp [fch, Fn]
    rw [e]
    convert h using 1
    simp only [fch, if_neg (show (0 : ℕ) + 1 ≠ 0 by omega), zero_add, pow_one, Pz, evalZ_P1]
    have : Us U0 s - 1 ≠ 0 := by linarith
    have : Us U0 s ≠ 0 := by linarith
    field_simp
    try ring
  · have e : fch U0 (m + 1) = fun s => (aC / 2) ^ (m + 1) * evalZ (Pz (m + 1)) (Us U0 s) := by
      funext s; simp [fch]
    rw [e]
    have := (hasDerivAt_evalZ hU0 hs (Pz (m + 1))).const_mul ((aC / 2) ^ (m + 1))
    convert this using 1
    simp only [fch, if_neg (show m + 1 + 1 ≠ 0 by omega), Pz, evalZ_normZ]
    ring

/-! ## `Q`-form -/

noncomputable def evalQZ (Q : UWZ) (u ω : ℝ) : ℝ :=
  (Q.map fun x => (x.2.2 : ℝ) * u ^ x.1 * ω ^ x.2.1).sum

theorem evalZ_eq_Q (m : ℕ) (P : UWZ) (h : okQ m P = true) {U : ℝ} (hU : 1 < U) :
    evalZ P U = (U⁻¹) ^ (2 * m - 1) * evalQZ (toQ m P) U⁻¹ (U / (U - 1)) := by
  induction P with
  | nil => simp [evalZ, evalQZ, toQ]
  | cons x P ih =>
    simp only [okQ, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [evalZ_cons, ih h.2]
    simp only [evalQZ, toQ, List.map_cons, List.sum_cons]
    have hU1 : U - 1 ≠ 0 := by linarith
    have hU0 : U ≠ 0 := by linarith
    have key : (U⁻¹) ^ x.1 * ((U - 1)⁻¹) ^ x.2.1 =
        (U⁻¹) ^ (2 * m - 1) * ((U⁻¹) ^ (x.1 + x.2.1 - (2 * m - 1)) * (U / (U - 1)) ^ x.2.1) := by
      rw [← mul_assoc, ← pow_add, show 2 * m - 1 + (x.1 + x.2.1 - (2 * m - 1)) = x.1 + x.2.1 by omega,
        pow_add, div_eq_mul_inv, mul_pow]
      have hq : (U⁻¹) ^ x.2.1 * U ^ x.2.1 = 1 := by rw [← mul_pow, inv_mul_cancel₀ hU0, one_pow]
      linear_combination (-((U⁻¹) ^ x.1 * ((U - 1)⁻¹) ^ x.2.1)) * hq
    have : (x.2.2 : ℝ) * (U⁻¹) ^ x.1 * ((U - 1)⁻¹) ^ x.2.1 =
        (U⁻¹) ^ (2 * m - 1) * ((x.2.2 : ℝ) * (U⁻¹) ^ (x.1 + x.2.1 - (2 * m - 1)) * (U / (U - 1)) ^ x.2.1) := by
      rw [mul_assoc, key]; ring
    rw [this]; ring

end JensenThreshold.Tail
