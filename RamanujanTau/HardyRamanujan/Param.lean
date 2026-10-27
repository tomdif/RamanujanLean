/-
# The saddle-point parametrization

`t = π/√(6n)`, `A = nt = π²/(6t)` (so `2A = π√(2n/3)`). On the major arc, with `θ = tv/√A`, `z = t + iθ`:
`√(z/2π)·e^{π²/(6z) − z/24}·e^{nz} = √(t/2π)·e^{2A}·h(v/√A, t, v)`.
-/
import RamanujanTau.HardyRamanujan.Major

set_option autoImplicit false

namespace HardyRamanujan
open Complex Filter
open scoped Real Topology

noncomputable def tn (n : ℕ) : ℝ := π / √(6 * n)
noncomputable def An (n : ℕ) : ℝ := n * tn n

lemma tn_pos {n : ℕ} (hn : 1 ≤ n) : 0 < tn n := by
  unfold tn; have : (0 : ℝ) < 6 * n := by positivity
  exact div_pos Real.pi_pos (Real.sqrt_pos.mpr this)

lemma An_pos {n : ℕ} (hn : 1 ≤ n) : 0 < An n := by
  unfold An; have := tn_pos hn; positivity

lemma An_eq {n : ℕ} (hn : 1 ≤ n) : π ^ 2 / (6 * tn n) = An n := by
  have ht := tn_pos hn
  have h6 : (0 : ℝ) < 6 * n := by positivity
  have hs : √(6 * n) ^ 2 = 6 * n := Real.sq_sqrt h6.le
  unfold An
  rw [div_eq_iff (by positivity)]
  unfold tn
  field_simp
  rw [mul_comm (n : ℝ) 6, hs]

lemma two_An {n : ℕ} (hn : 1 ≤ n) : 2 * An n = π * √(2 * n / 3) := by
  have h6 : (0 : ℝ) < 6 * n := by positivity
  unfold An tn
  have hs : √(6 * n) = 3 * √(2 * n / 3) := by
    rw [show (6 : ℝ) * n = 3 ^ 2 * (2 * n / 3) by ring, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have hpos : 0 < √(2 * n / 3) := Real.sqrt_pos.mpr (by positivity)
  have hsq : √(2 * n / 3) ^ 2 = 2 * n / 3 := Real.sq_sqrt (by positivity)
  rw [hs]
  field_simp
  nlinarith [hsq]

/-- the main integrand `M(θ) = √(z/2π) e^{π²/(6z) − z/24} e^{nz}`. -/
noncomputable def Mfun (n : ℕ) (t θ : ℝ) : ℂ :=
  sq (zt t θ) * cexp (π ^ 2 / (6 * zt t θ) - zt t θ / 24) * cexp (n * zt t θ)

lemma sq_scale {t : ℝ} (ht : 0 < t) (u : ℝ) :
    sq ((t : ℂ) * (1 + u * I)) = ((√(t / (2 * π)) : ℝ) : ℂ) * cexp (log (1 + u * I) / 2) := by
  have h2π : 0 < t / (2 * π) := by positivity
  unfold sq
  rw [show (t : ℂ) * (1 + u * I) / (2 * π) = ((t / (2 * π) : ℝ) : ℂ) * (1 + u * I) by push_cast; ring,
    Complex.log_ofReal_mul h2π (one_add_ne_zero u), add_div, Complex.exp_add]
  congr 1
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos h2π, Complex.ofReal_exp]
  push_cast; ring_nf

/-- **the parametrization**. -/
lemma Mfun_scale {n : ℕ} (hn : 1 ≤ n) (v : ℝ) :
    Mfun n (tn n) (tn n / √(An n) * v) =
      ((√(tn n / (2 * π)) : ℝ) : ℂ) * ((Real.exp (2 * An n) : ℝ) : ℂ) * hfun (v / √(An n)) (tn n) v := by
  have ht := tn_pos hn
  have hA := An_pos hn
  have hsA : 0 < √(An n) := Real.sqrt_pos.mpr hA
  set t := tn n with htdef
  set A := An n with hAdef
  set u := v / √A with hu
  have hz : zt t (t / √A * v) = (t : ℂ) * (1 + u * I) := by
    simp only [zt, hu]; push_cast; field_simp
  have hAt : (A : ℂ) = n * t := by rw [hAdef, An]; push_cast; ring
  have hAπ : (π : ℂ) ^ 2 / (6 * t) = A := by
    have := An_eq hn; rw [← htdef, ← hAdef] at this; exact_mod_cast this
  have hu2 : (A : ℂ) * (u : ℂ) ^ 2 = (v : ℂ) ^ 2 := by
    rw [hu]; push_cast
    have : (√A : ℂ) ^ 2 = A := by exact_mod_cast Real.sq_sqrt hA.le
    have hA0 : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
    field_simp
    rw [this]
    field_simp
  have hw := one_add_ne_zero u
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hexp : π ^ 2 / (6 * zt t (t / √A * v)) - zt t (t / √A * v) / 24 + n * zt t (t / √A * v) =
      2 * A + (-((t : ℂ) * (1 + u * I)) / 24) + (-((v : ℂ) ^ 2 / (1 + u * I))) := by
    rw [hz, ← hu2]
    have h1 : (π : ℂ) ^ 2 / (6 * (t * (1 + u * I))) = A / (1 + u * I) := by
      rw [← hAπ]; field_simp
    rw [h1, hAt]
    field_simp
    ring_nf
    rw [I_sq]
    ring
  unfold Mfun
  rw [mul_assoc, ← Complex.exp_add, hexp, hz, sq_scale ht, Complex.exp_add, Complex.exp_add, ofReal_exp]
  unfold hfun
  push_cast
  ring

end HardyRamanujan
