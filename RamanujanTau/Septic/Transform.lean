/-
# Rebák's Lemma 2.1: `φ(e^{−π/√n}) = n^{1/4} φ(e^{−π√n})`

From Mathlib's `jacobiTheta₂_functional_equation` at `z = 0`, `τ = i t`:
`θ(it) = t^{−1/2} θ(i/t)` with `θ(it) = Σ_n e^{−π n² t} = phiR (e^{−πt})`.
-/
import RamanujanTau.Septic.Page206
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

namespace RamanujanTau.Septic

open Real Complex

/-- `jacobiTheta (i t) = phiR (e^{−πt})` (as complex numbers), `t > 0`. -/
lemma jacobiTheta_I_mul (t : ℝ) :
    jacobiTheta (I * t) = ((phiR (Real.exp (-π * t)) : ℝ) : ℂ) := by
  rw [jacobiTheta, phiR, Complex.ofReal_tsum]
  congr 1; funext n
  rw [← Real.exp_nat_mul, Complex.ofReal_exp]
  congr 1
  have h : ((n.natAbs : ℂ)) ^ 2 = (n : ℂ) ^ 2 := by
    have := congrArg (fun z : ℤ => (z : ℂ)) (Int.natAbs_sq n)
    simpa only [Int.cast_pow, Int.cast_natCast] using this
  push_cast
  rw [h]
  ring_nf
  rw [Complex.I_sq]; ring

/-- `φ(e^{−π t}) > 0`-free form of the modular transformation: `φ(e^{−π/t}) = √t · φ(e^{−π t})`. -/
theorem phiR_transform {t : ℝ} (ht : 0 < t) :
    phiR (Real.exp (-π / t)) = √t * phiR (Real.exp (-π * t)) := by
  have hfe := jacobiTheta₂_functional_equation 0 (I * t)
  rw [← jacobiTheta_eq_jacobiTheta₂] at hfe
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have e1 : -I * (I * (t : ℂ)) = (t : ℂ) := by ring_nf; rw [Complex.I_sq]; ring
  have e2 : (-1 : ℂ) / (I * t) = I * ((1 / t : ℝ) : ℂ) := by
    push_cast; field_simp; rw [Complex.I_sq]
  rw [e1, e2, zero_div, ← jacobiTheta_eq_jacobiTheta₂] at hfe
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
    Complex.exp_zero, mul_one] at hfe
  rw [jacobiTheta_I_mul, jacobiTheta_I_mul] at hfe
  have hs : ((t : ℂ) ^ (1 / 2 : ℂ)) = ((√t : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ht.le]; push_cast; rfl
  rw [hs] at hfe
  have hsq : 0 < √t := Real.sqrt_pos.mpr ht
  have hfe' : ((phiR (Real.exp (-π * t)) : ℝ) : ℂ) * ((√t : ℝ) : ℂ)
      = ((phiR (Real.exp (-π * (1 / t))) : ℝ) : ℂ) := by
    rw [hfe]; field_simp [show ((√t : ℝ) : ℂ) ≠ 0 by exact_mod_cast hsq.ne']
  have := congrArg Complex.re hfe'
  simp only [← Complex.ofReal_mul, Complex.ofReal_re] at this
  rw [show -π / t = -π * (1 / t) by ring, ← this]; ring

/-- **Rebák, Lemma 2.1.** For `n > 0`: `φ(e^{−π/√n}) = n^{1/4} φ(e^{−π√n})`. -/
theorem rebak_lemma_2_1 {n : ℝ} (hn : 0 < n) :
    phiR (Real.exp (-π / √n)) = n ^ (1 / 4 : ℝ) * phiR (Real.exp (-π * √n)) := by
  rw [phiR_transform (Real.sqrt_pos.mpr hn)]
  congr 1
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hn.le]
  norm_num

end RamanujanTau.Septic
