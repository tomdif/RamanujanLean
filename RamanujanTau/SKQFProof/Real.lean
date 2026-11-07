/-
# Reality of `𝒮⁰(v)` and of `𝒮(0)`; the real part of `𝒜(v, L)`

* `S0v_im`: `𝒮⁰(v)` is **real** for real `v`.  The phase of the `(a,b,c,d)` term is
  `(P₁d/c)^{iv}(P₁Q₁)^{−iv/2} = (a/c)^{iv/2}(d/b)^{iv/2}`, which is conjugated by the involution
  `(a,b,c,d) ↦ (c,d,a,b)` (that fixes `κ`, `P₁`, `Q₁`).
* `Sv_zero_real`: `𝒮(0)` is real.
* `re_Av_eq`: hence, for `v ≠ 0` and `𝒮(v) = F₀ + v·G` with `F₀` real,
  `Re 𝒜(v,L) = γ_R Re(e^{−ivL}𝒮(v)) + r₀F₀·L·sinc(vL) − r₀ Im(e^{−ivL} G)`:
  the `𝒮⁰`-term of `𝒜` has **zero real part** and drops out of `SKQFHyp` (ii).
Level 1.
-/
import RamanujanTau.SelbergKey.Arith
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

set_option autoImplicit false

namespace RamanujanTau.SKQFProof

open Complex Finset
open RamanujanTau.SelbergKey

/-- The real phase of the `𝒮⁰` term. -/
noncomputable def phi0 (a b c d : ℕ) : ℝ :=
  Real.log (P1 a b c d) + Real.log d - Real.log c - Real.log (P1 a b c d * Q1 a b c d : ℕ) / 2

lemma P1_swap (a b c d : ℕ) : P1 c d a b = P1 a b c d := by
  unfold P1; rw [mul_comm c a, mul_comm d b]

lemma Q1_swap (a b c d : ℕ) : Q1 c d a b = Q1 a b c d := by
  unfold Q1; rw [mul_comm c a, mul_comm d b]

lemma kap_swap (y a b c d : ℕ) : kap y c d a b = kap y a b c d := by
  unfold kap; rw [mul_comm c a, mul_comm d b]; ring_nf

lemma P1_mul_gcd (a b c d : ℕ) : P1 a b c d * Nat.gcd (a * c) (b * d) = a * c :=
  Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)

lemma Q1_mul_gcd (a b c d : ℕ) : Q1 a b c d * Nat.gcd (a * c) (b * d) = b * d :=
  Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)

lemma log_P1 {a b c d : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d) :
    Real.log (P1 a b c d) = Real.log a + Real.log c - Real.log (Nat.gcd (a * c) (b * d)) := by
  have hg : 0 < Nat.gcd (a * c) (b * d) := Nat.gcd_pos_of_pos_left _ (by positivity)
  have hP : 0 < P1 a b c d := by
    have h := P1_mul_gcd a b c d
    rcases Nat.eq_zero_or_pos (P1 a b c d) with h0 | h0
    · rw [h0, zero_mul] at h; exact absurd h.symm (by positivity)
    · exact h0
  have e : ((P1 a b c d : ℕ) : ℝ) * (Nat.gcd (a * c) (b * d) : ℕ) = (a : ℝ) * c := by
    exact_mod_cast P1_mul_gcd a b c d
  have := congrArg Real.log e
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)] at this
  linarith

lemma log_Q1 {a b c d : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d) :
    Real.log (Q1 a b c d) = Real.log b + Real.log d - Real.log (Nat.gcd (a * c) (b * d)) := by
  have hg : 0 < Nat.gcd (a * c) (b * d) := Nat.gcd_pos_of_pos_left _ (by positivity)
  have hQ : 0 < Q1 a b c d := by
    have h := Q1_mul_gcd a b c d
    rcases Nat.eq_zero_or_pos (Q1 a b c d) with h0 | h0
    · rw [h0, zero_mul] at h; exact absurd h.symm (by positivity)
    · exact h0
  have e : ((Q1 a b c d : ℕ) : ℝ) * (Nat.gcd (a * c) (b * d) : ℕ) = (b : ℝ) * d := by
    exact_mod_cast Q1_mul_gcd a b c d
  have := congrArg Real.log e
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)] at this
  linarith

lemma phi0_swap {a b c d : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d) :
    phi0 c d a b = -phi0 a b c d := by
  unfold phi0
  rw [P1_swap, Q1_swap]
  have hP := log_P1 ha hb hc hd
  have hQ := log_Q1 ha hb hc hd
  have hg : 0 < Nat.gcd (a * c) (b * d) := Nat.gcd_pos_of_pos_left _ (by positivity)
  have hPpos : (0 : ℝ) < P1 a b c d := by
    have h := P1_mul_gcd a b c d
    have : 0 < P1 a b c d := Nat.pos_of_ne_zero fun h0 => by
      rw [h0, zero_mul] at h; exact absurd h.symm (by positivity)
    exact_mod_cast this
  have hQpos : (0 : ℝ) < Q1 a b c d := by
    have h := Q1_mul_gcd a b c d
    have : 0 < Q1 a b c d := Nat.pos_of_ne_zero fun h0 => by
      rw [h0, zero_mul] at h; exact absurd h.symm (by positivity)
    exact_mod_cast this
  have hPQ : Real.log ((P1 a b c d * Q1 a b c d : ℕ) : ℝ) =
      Real.log (P1 a b c d) + Real.log (Q1 a b c d) := by
    push_cast; exact Real.log_mul hPpos.ne' hQpos.ne'
  rw [hPQ]
  linarith

/-- The `𝒮⁰` summand in the form `κ e^{iv φ₀} ρ ρ`. -/
lemma S0_term_eq (y a b c d : ℕ) (v : ℝ) :
    (kap y a b c d : ℂ) * ev a b c d v *
      cexp (-((v : ℂ) * I * ((Real.log (P1 a b c d * Q1 a b c d : ℕ) / 2 : ℝ) : ℂ))) *
      ((HafnerBridge.rho (P1 a b c d) * HafnerBridge.rho (Q1 a b c d) : ℝ) : ℂ) =
    (kap y a b c d : ℂ) * cexp ((v : ℂ) * I * (phi0 a b c d : ℂ)) *
      ((HafnerBridge.rho (P1 a b c d) * HafnerBridge.rho (Q1 a b c d) : ℝ) : ℂ) := by
  unfold ev phi0
  rw [mul_assoc (kap y a b c d : ℂ), ← Complex.exp_add]
  congr 3
  push_cast
  ring

lemma sum4_swap (y : ℕ) (f : ℕ → ℕ → ℕ → ℕ → ℂ) :
    sum4 y (fun a b c d => f c d a b) = sum4 y f := by
  unfold sum4
  -- Σ_a Σ_b Σ_c Σ_d f c d a b
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm]
  rw [Finset.sum_comm]

/-- **`𝒮⁰(v)` is real.** -/
theorem S0v_im (y : ℕ) (v : ℝ) : (S0v y v).im = 0 := by
  set t : ℕ → ℕ → ℕ → ℕ → ℂ := fun a b c d => (kap y a b c d : ℂ) *
    cexp ((v : ℂ) * I * (phi0 a b c d : ℂ)) *
      ((HafnerBridge.rho (P1 a b c d) * HafnerBridge.rho (Q1 a b c d) : ℝ) : ℂ) with ht
  have hS : S0v y v = sum4 y t := by
    unfold S0v; simp_rw [S0_term_eq]; rfl
  have key : ∀ a b c d : ℕ, 1 ≤ a → 1 ≤ b → 1 ≤ c → 1 ≤ d →
      (starRingEnd ℂ) (t a b c d) = t c d a b := by
    intro a b c d ha hb hc hd
    simp only [ht]
    rw [kap_swap, P1_swap, Q1_swap, phi0_swap ha hb hc hd]
    simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I]
    congr 2
    push_cast
    ring
  have hconj : (starRingEnd ℂ) (S0v y v) = S0v y v := by
    rw [hS]
    calc (starRingEnd ℂ) (sum4 y t) = sum4 y (fun a b c d => t c d a b) := by
          unfold sum4
          simp only [map_sum]
          refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb =>
            Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun d hd => ?_
          exact key a b c d (Finset.mem_Icc.1 ha).1 (Finset.mem_Icc.1 hb).1
            (Finset.mem_Icc.1 hc).1 (Finset.mem_Icc.1 hd).1
      _ = sum4 y t := sum4_swap y t
  exact Complex.conj_eq_iff_im.1 hconj

/-- `N_p(a, 1)` is real. -/
lemma NpC_one_real (p a : ℕ) :
    NpC p a 1 = ((∑' j : ℕ, HafnerBridge.lam (p ^ (j + a)) * HafnerBridge.lam (p ^ j) *
      (p : ℝ) ^ (-(j : ℝ)) : ℝ) : ℂ) := by
  unfold NpC
  rw [Complex.ofReal_tsum]
  congr 1; funext j
  push_cast
  rw [mul_one, Complex.ofReal_cpow (by positivity)]
  push_cast; ring_nf

lemma DpC_one_real (p : ℕ) :
    DpC p 1 = ((∑' j : ℕ, HafnerBridge.lam (p ^ j) ^ 2 * (p : ℝ) ^ (-(j : ℝ)) : ℝ) : ℂ) := by
  unfold DpC
  rw [Complex.ofReal_tsum]
  congr 1; funext j
  push_cast
  rw [mul_one, Complex.ofReal_cpow (by positivity)]
  push_cast; ring_nf

lemma rhoC_one_real (m : ℕ) : ∃ r : ℝ, rhoC m 1 = r := by
  unfold rhoC
  refine ⟨∏ p ∈ m.primeFactors,
    (∑' j : ℕ, HafnerBridge.lam (p ^ (j + m.factorization p)) * HafnerBridge.lam (p ^ j) *
      (p : ℝ) ^ (-(j : ℝ))) / (∑' j : ℕ, HafnerBridge.lam (p ^ j) ^ 2 * (p : ℝ) ^ (-(j : ℝ))), ?_⟩
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [NpC_one_real, DpC_one_real, Complex.ofReal_div]

/-- **`𝒮(0)` is real.** -/
theorem Sv_zero_im (y : ℕ) : (Sv y 0).im = 0 := by
  unfold Sv sum4
  simp only [Complex.im_sum]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
    Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
  obtain ⟨r, hr⟩ := rhoC_one_real (P1 a b c d)
  obtain ⟨s, hs⟩ := rhoC_one_real (Q1 a b c d)
  have he : ev a b c d 0 = 1 := by unfold ev; simp
  simp only [Complex.ofReal_zero, zero_mul, sub_zero, he, hr, hs, mul_one]
  simp [Complex.mul_im]

/-- **The real part of `𝒜`.** -/
theorem re_Av_eq (y : ℕ) {v : ℝ} (hv : v ≠ 0) (L F0 : ℝ) (G : ℂ)
    (hS : Sv y v = (F0 : ℂ) + (v : ℂ) * G) :
    (Av y v L).re =
      GoodSecondTerm.gammaD * (cexp (-((v * L : ℝ) : ℂ) * I) * Sv y v).re +
        HafnerBridge.r0 * F0 * (L * Real.sinc (v * L)) -
        HafnerBridge.r0 * (cexp (-((v * L : ℝ) : ℂ) * I) * G).im := by
  have hS0 : S0v y v = ((S0v y v).re : ℂ) := by
    apply Complex.ext <;> simp [S0v_im]
  set E := cexp (-((v * L : ℝ) : ℂ) * I) with hE
  have hEre : E.re = Real.cos (v * L) := by
    rw [hE, show -((v * L : ℝ) : ℂ) * I = ((-(v * L) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  have hEim : E.im = -Real.sin (v * L) := by
    rw [hE, show -((v * L : ℝ) : ℂ) * I = ((-(v * L) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_ofReal_mul_I_im, Real.sin_neg]
  have hsinc : L * Real.sinc (v * L) = Real.sin (v * L) / v := by
    rcases eq_or_ne L 0 with hL | hL
    · simp [hL]
    · rw [Real.sinc_of_ne_zero (mul_ne_zero hv hL)]; field_simp
  have hdiv : (HafnerBridge.r0 : ℂ) / ((v : ℂ) * I) = -I * ((HafnerBridge.r0 / v : ℝ) : ℂ) := by
    have hv' : (v : ℂ) ≠ 0 := by exact_mod_cast hv
    push_cast
    field_simp
    rw [Complex.I_sq]; ring
  unfold Av
  rw [← hE, hdiv, hS0, hsinc, hS]
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_im, hEre, hEim]
  field_simp
  ring

end RamanujanTau.SKQFProof
