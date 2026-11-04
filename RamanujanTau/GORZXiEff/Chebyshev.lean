/-
# Turán inequalities from a monotone kernel ratio (Chebyshev's covariance inequality)

Abstract part of the Csordas–Norfolk–Varga / Csordas–Varga route to the Turán inequalities for the
Taylor coefficients of Riemann's `Ξ`.

Let `Φ > 0` on `(0,∞)` with derivative `Φ'`, polynomial moments `b(m) = ∫_0^∞ u^m Φ(u) du`, and suppose

  `R(u) = −Φ'(u) / (u Φ(u))` is monotone (nondecreasing) on `(0,∞)`

(equivalently: `log Φ(√v)` is concave in `v > 0`).  Then for every `n`

  `(2n+1) · b(2n) · b(2n+4) ≤ (2n+3) · b(2n+2)²`        (**`turan_mom`**).

Proof: integration by parts gives `∫ u^{m+1} Φ' = −(m+1) b(m)`; with the weight `w = u^{2n+2}Φ` and
`m̄ = ∫u²w/∫w`, the integrand `(u² − m̄)(R(u) − R(√m̄)) w(u)` is pointwise `≥ 0` (one-point form of Chebyshev's
inequality), and its integral is `(2n+3) b(2n+2) − m̄ (2n+1) b(2n)`.
-/
import RamanujanTau.GORZXi.Core

set_option autoImplicit false

namespace GORZXiEff

open Real Set MeasureTheory Filter Topology

/-- polynomial moments on `(0,∞)`. -/
noncomputable def mom (Φ : ℝ → ℝ) (m : ℕ) : ℝ := ∫ u in Ioi (0 : ℝ), u ^ m * Φ u

/-- regularity/decay hypotheses on a kernel (all routine for Riemann's `Φ`). -/
structure KernelReg (Φ Φ' : ℝ → ℝ) : Prop where
  deriv : ∀ u : ℝ, HasDerivAt Φ (Φ' u) u
  pos : ∀ u : ℝ, 0 < u → 0 < Φ u
  int : ∀ m : ℕ, IntegrableOn (fun u => u ^ m * Φ u) (Ioi 0)
  int' : ∀ m : ℕ, IntegrableOn (fun u => u ^ m * Φ' u) (Ioi 0)
  decay : ∀ m : ℕ, Tendsto (fun u => u ^ m * Φ u) atTop (𝓝 0)

/-- what the Chebyshev argument actually uses: positivity, integrability, and the integration-by-parts
identities `∫_0^∞ u^{m+1}Φ' = −(m+1) ∫_0^∞ u^m Φ` (here `Φ'` need not be given as a derivative). -/
structure KernelMom (Φ Φ' : ℝ → ℝ) : Prop where
  pos : ∀ u : ℝ, 0 < u → 0 < Φ u
  int : ∀ m : ℕ, IntegrableOn (fun u => u ^ m * Φ u) (Ioi 0)
  int' : ∀ m : ℕ, IntegrableOn (fun u => u ^ m * Φ' u) (Ioi 0)
  ibp : ∀ m : ℕ, ∫ u in Ioi (0 : ℝ), u ^ (m + 1) * Φ' u = -((m + 1 : ℝ) * mom Φ m)

/-- the ratio `R(u) = −Φ'(u)/(uΦ(u))`. -/
noncomputable def ratioR (Φ Φ' : ℝ → ℝ) (u : ℝ) : ℝ := -Φ' u / (u * Φ u)

variable {Φ Φ' : ℝ → ℝ}

/-- integration by parts: `∫_0^∞ u^{m+1} Φ' = −(m+1) ∫_0^∞ u^m Φ`. -/
lemma ibp_of (hd : ∀ u : ℝ, HasDerivAt Φ (Φ' u) u) (m : ℕ)
    (hi : IntegrableOn (fun u => u ^ m * Φ u) (Ioi 0))
    (hi' : IntegrableOn (fun u => u ^ (m + 1) * Φ' u) (Ioi 0))
    (hdec : Tendsto (fun u => u ^ (m + 1) * Φ u) atTop (𝓝 0)) :
    ∫ u in Ioi (0 : ℝ), u ^ (m + 1) * Φ' u = -((m + 1 : ℝ) * mom Φ m) := by
  have hcont : Continuous Φ := continuous_iff_continuousAt.2 fun u => (hd u).continuousAt
  have key := integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (a' := 0) (b' := 0)
    (u := fun x : ℝ => x ^ (m + 1)) (u' := fun x => ((m + 1 : ℕ) : ℝ) * x ^ m) (v := Φ) (v' := Φ')
    (fun x _ => by simpa using hasDerivAt_pow (m + 1) x) (fun x _ => hd x)
    hi' (by
      have := hi.const_mul ((m + 1 : ℕ) : ℝ)
      refine IntegrableOn.congr_fun this (fun x _ => ?_) measurableSet_Ioi
      simp only [Pi.mul_apply]; ring)
    (by
      have : Tendsto (fun x : ℝ => x ^ (m + 1) * Φ x) (𝓝 0) (𝓝 (0 ^ (m + 1) * Φ 0)) :=
        ((continuous_pow (m + 1)).mul hcont).tendsto 0
      simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow,
        zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds)
    hdec
  rw [key, mom]
  have : ∫ x in Ioi (0 : ℝ), ((m + 1 : ℕ) : ℝ) * x ^ m * Φ x =
      ((m + 1 : ℕ) : ℝ) * ∫ x in Ioi (0 : ℝ), x ^ m * Φ x := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  rw [this]; push_cast; ring

lemma KernelReg.toMom (h : KernelReg Φ Φ') : KernelMom Φ Φ' :=
  ⟨h.pos, h.int, h.int', fun m => ibp_of h.deriv m (h.int m) (h.int' (m + 1)) (h.decay (m + 1))⟩

lemma mom_pos (h : KernelMom Φ Φ') (m : ℕ) : 0 < mom Φ m := by
  unfold mom
  rw [setIntegral_pos_iff_support_of_nonneg_ae _ (h.int m)]
  · have : Ioi (0 : ℝ) ⊆ Function.support (fun u => u ^ m * Φ u) := fun u hu =>
      (mul_pos (pow_pos hu m) (h.pos u hu)).ne'
    rw [inter_eq_right.2 this]; simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (mul_pos (pow_pos hu m) (h.pos u hu)).le

/-- **Turán inequality for the even moments** of a kernel with monotone `R = −Φ'/(uΦ)`. -/
theorem turan_mom (h : KernelMom Φ Φ') (hR : MonotoneOn (ratioR Φ Φ') (Ioi 0)) (n : ℕ) :
    (2 * n + 1 : ℝ) * mom Φ (2 * n) * mom Φ (2 * n + 4) ≤ (2 * n + 3 : ℝ) * mom Φ (2 * n + 2) ^ 2 := by
  set M0 := mom Φ (2 * n + 2) with hM0
  set M2 := mom Φ (2 * n + 4) with hM2
  have hM0p : 0 < M0 := mom_pos h _
  have hM2p : 0 < M2 := mom_pos h _
  set m := M2 / M0 with hm
  have hmp : 0 < m := div_pos hM2p hM0p
  set c := ratioR Φ Φ' (Real.sqrt m) with hc
  have hsq : 0 < Real.sqrt m := Real.sqrt_pos.2 hmp
  -- pointwise nonnegativity
  have hnn : 0 ≤ ∫ u in Ioi (0 : ℝ), (u ^ 2 - m) * (ratioR Φ Φ' u - c) * (u ^ (2 * n + 2) * Φ u) := by
    refine setIntegral_nonneg measurableSet_Ioi fun u hu => ?_
    have hu' : (0 : ℝ) < u := hu
    have hw : 0 ≤ u ^ (2 * n + 2) * Φ u := (mul_pos (pow_pos hu' _) (h.pos u hu')).le
    refine mul_nonneg ?_ hw
    rcases le_or_gt m (u ^ 2) with h1 | h1
    · have : Real.sqrt m ≤ u := by
        rw [Real.sqrt_le_left]; · exact h1
        · exact hu'.le
      exact mul_nonneg (by linarith) (by linarith [hR hsq hu this])
    · have : u ≤ Real.sqrt m := by
        rw [Real.le_sqrt hu'.le hmp.le]; exact h1.le
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith [hR hu hsq this])
  -- evaluate the integral
  have hEq : ∀ u ∈ Ioi (0 : ℝ), (u ^ 2 - m) * (ratioR Φ Φ' u - c) * (u ^ (2 * n + 2) * Φ u) =
      (-(u ^ (2 * n + 3) * Φ' u) - c * (u ^ (2 * n + 4) * Φ u)) +
        (m * (u ^ (2 * n + 1) * Φ' u) + m * c * (u ^ (2 * n + 2) * Φ u)) := by
    intro u hu
    have hu' : (0 : ℝ) < u := hu
    have hp := (h.pos u hu').ne'
    unfold ratioR
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hEq] at hnn
  have i1 := h.int' (2 * n + 3)
  have i2 := h.int (2 * n + 4)
  have i3 := h.int' (2 * n + 1)
  have i4 := h.int (2 * n + 2)
  have hI : ∫ u in Ioi (0 : ℝ), (-(u ^ (2 * n + 3) * Φ' u) - c * (u ^ (2 * n + 4) * Φ u)) +
        (m * (u ^ (2 * n + 1) * Φ' u) + m * c * (u ^ (2 * n + 2) * Φ u)) =
      -(∫ u in Ioi (0 : ℝ), u ^ (2 * n + 3) * Φ' u) - c * M2 +
        (m * (∫ u in Ioi (0 : ℝ), u ^ (2 * n + 1) * Φ' u) + m * c * M0) := by
    rw [integral_add, integral_sub, integral_add, integral_neg, integral_const_mul, integral_const_mul,
      integral_const_mul]
    · rfl
    · exact i3.const_mul m
    · exact i4.const_mul (m * c)
    · exact i1.neg
    · exact i2.const_mul c
    · exact i1.neg.sub (i2.const_mul c)
    · exact (i3.const_mul m).add (i4.const_mul (m * c))
  rw [hI] at hnn
  have e1 := h.ibp (2 * n + 2)
  have e3 := h.ibp (2 * n)
  rw [show 2 * n + 2 + 1 = 2 * n + 3 by ring] at e1
  rw [show 2 * n + 1 = 2 * n + 1 by ring] at e3
  rw [e1, e3] at hnn
  have hmM : m * M0 = M2 := by rw [hm]; field_simp
  have key : 0 ≤ (2 * n + 3 : ℝ) * M0 - m * ((2 * n + 1) * mom Φ (2 * n)) := by
    rw [← hM0] at hnn
    push_cast at hnn
    have hc' : m * c * M0 = c * M2 := by rw [← hmM]; ring
    linarith
  have := mul_le_mul_of_nonneg_left (sub_nonneg.1 key) hM0p.le
  rw [← mul_assoc, mul_comm M0 m, hmM] at this
  nlinarith [this]

end GORZXiEff
