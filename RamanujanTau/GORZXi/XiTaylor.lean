/-
# The Taylor coefficients of `(−1 + 4z²) Λ(1/2 + z)` (milestone M2, part 2) and GORZ Theorem 1 for them

* `gammaMathlib n = n!/(2n)! · Re (d/dz)^{2n} [(−1 + 4z²) · completedRiemannZeta (1/2 + z)] (0)` — GORZ's
  `γ(n)` of eq. (1), `(−1+4z²)Λ(1/2+z) = Σ γ(n) z^{2n}/n!`, computed from **Mathlib's** completed zeta.
* **`gammaMathlib_eq`** : `gammaMathlib n = gammaXi n = n!/(2n)! · 2^{1−2n} (32 C(2n,2) F(2n−2) − F(2n))`
  for `n ≥ 1` (GORZ (13)), unconditionally.  Proof: near `0`, `(−1+4z²)Λ(1/2+z) = 4 + (4z²−1)Λ₀(1/2+z)`;
  `Λ₀(1/2+z) = (M(1/4+z/2) + M(1/4−z/2))/2` (Riemann, `XiMellin`), and `M^{(m)} = mellin(log^m · A)`; an explicit
  derivative chain gives all iterated derivatives; at `z = 0`, `mellin(log^m A)(1/4) = 2F(m)`.
* **`xi_gorz_mathlib`** : GORZ Theorem 1 for `gammaMathlib`, conditional on `XiKernelHyp`.
-/
import RamanujanTau.GORZXi.XiMellin

set_option autoImplicit false

namespace GORZXi

open Filter Topology Set MeasureTheory Asymptotics HurwitzZeta JensenThreshold

/-- `L_m(z) = ½ (½)^m [M_m(1/4 + z/2) + (−1)^m M_m(1/4 − z/2)]`, `M_m = mellin (log^m · A)`. -/
noncomputable def Lch (m : ℕ) (z : ℂ) : ℂ :=
  (1 / 2) * ((1 / 2) ^ m * (mellin (Am m) (1 / 4 + z / 2) + (-1) ^ m * mellin (Am m) (1 / 4 - z / 2)))

lemma Lch_zero (z : ℂ) : Lch 0 z = completedRiemannZeta₀ (1 / 2 + z) := by
  rw [completedRiemannZeta₀_eq, Lch, Am_zero,
    show (1 / 2 + z) / 2 = 1 / 4 + z / 2 by ring, show (1 : ℂ) / 2 - (1 / 4 + z / 2) = 1 / 4 - z / 2 by ring]
  ring

lemma Lch_hasDerivAt (m : ℕ) (z : ℂ) : HasDerivAt (Lch m) (Lch (m + 1) z) z := by
  have h1 : HasDerivAt (fun z : ℂ => 1 / 4 + z / 2) (1 / 2) z := by
    simpa using ((hasDerivAt_id z).div_const 2).const_add (1 / 4 : ℂ)
  have h2 : HasDerivAt (fun z : ℂ => 1 / 4 - z / 2) (-(1 / 2)) z := by
    simpa using ((hasDerivAt_id z).div_const 2).const_sub (1 / 4 : ℂ)
  have hA := (hasDerivAt_mellin_Am m (1 / 4 + z / 2)).comp z h1
  have hB := (hasDerivAt_mellin_Am m (1 / 4 - z / 2)).comp z h2
  have := ((hA.add (hB.const_mul ((-1 : ℂ) ^ m))).const_mul ((1 / 2 : ℂ) ^ m)).const_mul (1 / 2 : ℂ)
  convert this using 1
  simp only [Lch, pow_succ]
  ring

/-- the derivative chain of `G(z) = 4 + (4z²−1) L_0(z)`. -/
noncomputable def Gch : ℕ → ℂ → ℂ
  | 0 => fun z => 4 + (4 * z ^ 2 - 1) * Lch 0 z
  | 1 => fun z => (4 * z ^ 2 - 1) * Lch 1 z + 8 * z * Lch 0 z
  | k + 2 => fun z => (4 * z ^ 2 - 1) * Lch (k + 2) z + 8 * ((k : ℂ) + 2) * z * Lch (k + 1) z +
      4 * ((k : ℂ) + 2) * ((k : ℂ) + 1) * Lch k z

lemma hq (z : ℂ) : HasDerivAt (fun z : ℂ => 4 * z ^ 2 - 1) (8 * z) z := by
  have := ((hasDerivAt_pow 2 z).const_mul (4 : ℂ)).sub_const 1
  convert this using 1; ring

lemma hlin (c z : ℂ) : HasDerivAt (fun z : ℂ => c * z) c z := by
  simpa using (hasDerivAt_id z).const_mul c

lemma Gch_hasDerivAt (m : ℕ) (z : ℂ) : HasDerivAt (Gch m) (Gch (m + 1) z) z := by
  rcases m with _ | _ | k
  · have := ((hq z).mul (Lch_hasDerivAt 0 z)).const_add 4
    convert this using 1
    simp only [Gch]; ring
  · have := ((hq z).mul (Lch_hasDerivAt 1 z)).add ((hlin 8 z).mul (Lch_hasDerivAt 0 z))
    convert this using 1
    simp only [Gch]; push_cast; ring
  · have := (((hq z).mul (Lch_hasDerivAt (k + 2) z)).add
      ((hlin (8 * ((k : ℂ) + 2)) z).mul (Lch_hasDerivAt (k + 1) z))).add
      ((Lch_hasDerivAt k z).const_mul (4 * ((k : ℂ) + 2) * ((k : ℂ) + 1)))
    convert this using 1
    simp only [Gch]; push_cast; ring

lemma iteratedDeriv_chain (F : ℕ → ℂ → ℂ) (h : ∀ m z, HasDerivAt (F m) (F (m + 1) z) z) :
    ∀ m, iteratedDeriv m (F 0) = F m
  | 0 => iteratedDeriv_zero
  | m + 1 => by
    rw [iteratedDeriv_succ, iteratedDeriv_chain F h m]
    funext z; exact (h m z).deriv

lemma ev_iteratedDeriv {f g : ℂ → ℂ} {x : ℂ} (h : f =ᶠ[𝓝 x] g) :
    ∀ m, iteratedDeriv m f =ᶠ[𝓝 x] iteratedDeriv m g
  | 0 => by simpa using h
  | m + 1 => by simp only [iteratedDeriv_succ]; exact (ev_iteratedDeriv h m).deriv

/-- the function of GORZ eq. (1), from Mathlib's completed zeta. -/
noncomputable def xiFun (z : ℂ) : ℂ := (-1 + 4 * z ^ 2) * completedRiemannZeta (1 / 2 + z)

lemma xiFun_ev : xiFun =ᶠ[𝓝 0] Gch 0 := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  have h1 : (1 / 2 + z) ≠ 0 := by
    intro h
    have : z = -(1 / 2) := by linear_combination h
    rw [this, norm_neg] at hz; norm_num at hz
  have h2 : (1 - (1 / 2 + z)) ≠ 0 := by
    intro h
    have : z = 1 / 2 := by linear_combination -h
    rw [this] at hz; norm_num at hz
  have key : (-1 + 4 * z ^ 2) * (1 / (1 / 2 + z) + 1 / (1 - (1 / 2 + z))) = -4 := by
    rw [div_add_div _ _ h1 h2, mul_div_assoc', div_eq_iff (mul_ne_zero h1 h2)]
    ring
  simp only [xiFun, Gch, Lch_zero, completedRiemannZeta_eq]
  linear_combination (-1 : ℂ) * key

/-- **GORZ's `γ(n)`** (eq. (1)) from Mathlib's `completedRiemannZeta`. -/
noncomputable def gammaMathlib (n : ℕ) : ℝ :=
  (n.factorial : ℝ) / ((2 * n).factorial : ℝ) * (iteratedDeriv (2 * n) xiFun 0).re

lemma iteratedDeriv_xiFun (m : ℕ) : iteratedDeriv m xiFun 0 = Gch m 0 := by
  rw [(ev_iteratedDeriv xiFun_ev m).eq_of_nhds, iteratedDeriv_chain Gch Gch_hasDerivAt m]

/-- `mellin (log^m A)(1/4) = 2 F(m)`. -/
lemma mellin_Am_quarter (m : ℕ) : mellin (Am m) (1 / 4) = ((2 * FXi m : ℝ) : ℂ) := by
  unfold mellin
  rw [Am_eq_ind]
  have e : (fun t : ℝ => (t : ℂ) ^ ((1 / 4 : ℂ) - 1) • (Ioi 1).indicator
      (fun t => (Real.log t ^ m : ℝ) • (((evenKernel 0 t : ℝ) : ℂ) - 1)) t) =
      (Ioi 1).indicator (fun t : ℝ => ((Real.log t ^ m * t ^ (-(3 / 4 : ℝ)) * (2 * theta0 t) : ℝ) : ℂ)) := by
    funext t
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · have ht0 : (0 : ℝ) ≤ t := by simp only [mem_Ioi] at ht; linarith
      rw [indicator_of_mem ht, indicator_of_mem ht, smul_eq_mul, Complex.real_smul,
        show (1 / 4 : ℂ) - 1 = ((-(3 / 4 : ℝ) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow ht0]
      simp only [theta0]
      push_cast
      ring
    · rw [indicator_of_notMem ht, indicator_of_notMem ht, smul_zero]
  rw [e, setIntegral_indicator measurableSet_Ioi,
    show Ioi (0 : ℝ) ∩ Ioi 1 = Ioi 1 by ext x; simp only [mem_inter_iff, mem_Ioi]; constructor <;> intro h
                                        <;> [exact h.2; exact ⟨by linarith, h⟩],
    integral_complex_ofReal]
  congr 1
  rw [FXi, ← integral_const_mul]
  congr 1; funext t; ring

lemma Lch_even_zero (j : ℕ) : Lch (2 * j) 0 = (1 / 2) ^ (2 * j) * ((2 * FXi (2 * j) : ℝ) : ℂ) := by
  simp only [Lch, zero_div, add_zero, sub_zero]
  rw [← mellin_Am_quarter, show ((-1 : ℂ)) ^ (2 * j) = 1 by rw [pow_mul]; norm_num]
  ring

/-- **Riemann–GORZ formula (13), from Mathlib**: `γ(n) = n!/(2n)! · 2^{1−2n} (32 C(2n,2) F(2n−2) − F(2n))`. -/
theorem gammaMathlib_eq (n : ℕ) (hn : 1 ≤ n) : gammaMathlib n = gammaXi n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [gammaMathlib, iteratedDeriv_xiFun, show 2 * (k + 1) = 2 * k + 2 by ring]
  simp only [Gch, mul_zero, zero_mul, zero_add]
  rw [show 2 * k + 2 = 2 * (k + 1) by ring, Lch_even_zero (k + 1), Lch_even_zero k]
  simp only [gammaXi, aXi, BXi, show 2 * (k + 1) - 2 = 2 * k by omega]
  rw [Nat.cast_choose_two]
  push_cast
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
    Complex.neg_re, Complex.one_re, Complex.re_ofNat, Complex.im_ofNat, Complex.natCast_re,
    Complex.natCast_im, Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.one_im, Complex.mul_im,
    Complex.add_im, Complex.sub_im, Complex.neg_im]
  rw [show (1 / 2 : ℂ) ^ (2 * (k + 1)) = (((1 / 2 : ℝ) ^ (2 * (k + 1)) : ℝ) : ℂ) by push_cast; ring,
    show (1 / 2 : ℂ) ^ (2 * k) = (((1 / 2 : ℝ) ^ (2 * k) : ℝ) : ℂ) by push_cast; ring]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  simp
  rw [pow_mul, pow_mul, pow_succ]
  field_simp
  ring

/-! ## GORZ Theorem 1 for Mathlib's `γ(n)` -/

lemma jensenSeq_congr {α β : ℕ → ℝ} {N : ℕ} (h : ∀ m, N ≤ m → α m = β m) (d n : ℕ) (hn : N ≤ n) :
    jensenSeq α d n = jensenSeq β d n := by
  unfold jensenSeq
  exact Finset.sum_congr rfl fun j _ => by rw [h (n + j) (by omega)]

lemma Jhat_congr {α β : ℕ → ℝ} {N : ℕ} (h : ∀ m, N ≤ m → α m = β m) (δ : ℕ → ℝ) (d n : ℕ) (hn : N ≤ n) :
    Jhat α (fun n => α (n + 1) / α n) δ d n = Jhat β (fun n => β (n + 1) / β n) δ d n := by
  simp only [Jhat, jensenSeq_congr h d n hn, h n hn, h (n + 1) (by omega)]

/-- **GORZ Theorem 1 for `Ξ`** (Mathlib's `completedRiemannZeta`), conditional on `XiKernelHyp`:
for every `d`, `J^{d,n}_γ` is hyperbolic for all sufficiently large `n`, and the renormalized polynomials
converge to `H_d`. -/
theorem xi_gorz_mathlib (hyp : XiKernelHyp) (d : ℕ) :
    (∀ i, Tendsto (fun n => (Jhat gammaMathlib (fun n => gammaMathlib (n + 1) / gammaMathlib n) δXi d n).coeff i)
      atTop (𝓝 ((GORZ.H d).coeff i))) ∧
    (∀ K : Set ℝ, IsCompact K → TendstoUniformlyOn
      (fun n x => (Jhat gammaMathlib (fun n => gammaMathlib (n + 1) / gammaMathlib n) δXi d n).eval x)
      (fun x => (GORZ.H d).eval x) atTop K) ∧
    (∀ᶠ n in atTop, Hyperbolic (jensenSeq gammaMathlib d n)) := by
  obtain ⟨h1, h2, h3⟩ := xi_gorz hyp d
  have hc : ∀ m, 1 ≤ m → gammaMathlib m = gammaXi m := gammaMathlib_eq
  have hJ : ∀ᶠ n in atTop, Jhat gammaMathlib (fun n => gammaMathlib (n + 1) / gammaMathlib n) δXi d n =
      Jhat gammaXi (fun n => gammaXi (n + 1) / gammaXi n) δXi d n :=
    (eventually_ge_atTop 1).mono fun n hn => Jhat_congr hc δXi d n hn
  refine ⟨fun i => (h1 i).congr' (hJ.mono fun n hn => by beta_reduce; rw [hn]), fun K hK => ?_, ?_⟩
  · exact (h2 K hK).congr (hJ.mono fun n hn x _ => by simp only [hn])
  · filter_upwards [h3, eventually_ge_atTop 1] with n hn hn1
    rwa [jensenSeq_congr hc d n hn1]

end GORZXi
