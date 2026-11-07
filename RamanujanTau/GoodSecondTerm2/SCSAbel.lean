/-
# Abel summation against the shifted-convolution bound

For fixed `h ≥ 1` and `t > 0` let
`r(x) = (x(x+h))^{−1/2} e^{it log((x+h)/x)} V(log x + log(x+h) − 2 log(t/2π))`.
Then `‖r(x)‖ ≤ 2/x`, `‖r(M+1) − r(M)‖ ≤ (4 + 2th/M)/M²`, and with `SCS(1/21,1/21)`
(`SCSSharp2.shiftedConvolutionBound_sharp2`), for `a ≥ h`,

    ‖Σ_{M>a} λ(M)λ(M+h) r(M)‖ ≤ K h^{1/21} (a^{−1/42} + t h a^{−1−1/42}).
-/
import RamanujanTau.GoodSecondTerm2.Rankin2
import RamanujanTau.SCSSharp2.Main

set_option autoImplicit false

namespace RamanujanTau.GoodSecondTerm2

open Complex MeasureTheory Set Filter Topology Finset
open RamanujanTau.ZetaAFE RamanujanTau.GoodSecondTerm RamanujanTau.SubconvexityCond

/-- The weight `r_{t,h}(x)`. -/
noncomputable def rr (t h x : ℝ) : ℂ :=
  ((Real.exp (-((Real.log x + Real.log (x + h)) / 2)) : ℝ) : ℂ) *
    cexp (t * I * ((Real.log (x + h) - Real.log x : ℝ) : ℂ)) *
    ((V (Real.log x + Real.log (x + h) - 2 * ellT t) : ℝ) : ℂ)

lemma exp_neg_half_le {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) :
    Real.exp (-((Real.log x + Real.log (x + h)) / 2)) ≤ 1 / x := by
  have h1 : Real.log x ≤ Real.log (x + h) := Real.log_le_log hx (by linarith)
  calc Real.exp (-((Real.log x + Real.log (x + h)) / 2)) ≤ Real.exp (-(Real.log x)) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = 1 / x := by rw [Real.exp_neg, Real.exp_log hx, one_div]

lemma norm_rr_le (t : ℝ) {h x : ℝ} (hx : 0 < x) (hh : 0 ≤ h) : ‖rr t h x‖ ≤ 2 / x := by
  unfold rr
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), abs_of_nonneg (V_nonneg _), Complex.norm_exp]
  have he : (t * I * ((Real.log (x + h) - Real.log x : ℝ) : ℂ)).re = 0 := by simp
  rw [he, Real.exp_zero, mul_one]
  have h1 := exp_neg_half_le hx hh
  have h2 := V_le_two (Real.log x + Real.log (x + h) - 2 * ellT t)
  have h3 := V_nonneg (Real.log x + Real.log (x + h) - 2 * ellT t)
  calc Real.exp (-((Real.log x + Real.log (x + h)) / 2)) * V (Real.log x + Real.log (x + h) - 2 * ellT t)
      ≤ (1 / x) * 2 := by gcongr
    _ = 2 / x := by ring

/-- The derivative of `r`. -/
noncomputable def drr (t h x : ℝ) : ℂ :=
  ((Real.exp (-((Real.log x + Real.log (x + h)) / 2)) : ℝ) : ℂ) *
    cexp (t * I * ((Real.log (x + h) - Real.log x : ℝ) : ℂ)) *
    ((-(1 / x + 1 / (x + h)) / 2 : ℝ) * ((V (Real.log x + Real.log (x + h) - 2 * ellT t) : ℝ) : ℂ) +
      t * I * ((1 / (x + h) - 1 / x : ℝ) : ℂ) * ((V (Real.log x + Real.log (x + h) - 2 * ellT t) : ℝ) : ℂ) +
      ((-gk (Real.log x + Real.log (x + h) - 2 * ellT t) * (1 / x + 1 / (x + h)) : ℝ) : ℂ))

lemma hasDerivAt_rr (t : ℝ) {h x : ℝ} (hx : 0 < x) (hh : 0 ≤ h) :
    HasDerivAt (rr t h) (drr t h x) x := by
  have hxh : 0 < x + h := by linarith
  have hl1 : HasDerivAt (fun y : ℝ => Real.log y) (1 / x) x := by
    simpa using (hasDerivAt_id' x).log hx.ne'
  have hl2 : HasDerivAt (fun y : ℝ => Real.log (y + h)) (1 / (x + h)) x := by
    simpa using ((hasDerivAt_id' x).add_const h).log hxh.ne'
  have hA : HasDerivAt (fun y => Real.exp (-((Real.log y + Real.log (y + h)) / 2)))
      (Real.exp (-((Real.log x + Real.log (x + h)) / 2)) * (-((1 / x + 1 / (x + h)) / 2))) x :=
    ((hl1.add hl2).div_const 2).neg.exp
  have hE : HasDerivAt (fun y : ℝ => cexp (t * I * ((Real.log (y + h) - Real.log y : ℝ) : ℂ)))
      (cexp (t * I * ((Real.log (x + h) - Real.log x : ℝ) : ℂ)) * (t * I * ((1 / (x + h) - 1 / x : ℝ) : ℂ))) x :=
    (((hl2.sub hl1).ofReal_comp).const_mul (t * I)).cexp
  have hW : HasDerivAt (fun y => V (Real.log y + Real.log (y + h) - 2 * ellT t))
      (-gk (Real.log x + Real.log (x + h) - 2 * ellT t) * (1 / x + 1 / (x + h))) x := by
    have := (hasDerivAt_V (Real.log x + Real.log (x + h) - 2 * ellT t)).comp x ((hl1.add hl2).sub_const (2 * ellT t))
    convert this using 1
  have := ((hA.ofReal_comp.mul hE).mul hW.ofReal_comp)
  unfold rr drr
  convert this using 1
  simp only [Pi.mul_apply, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_add,
    Complex.ofReal_sub, Complex.ofReal_inv, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

lemma norm_drr_le (t : ℝ) (ht : 0 ≤ t) {h x : ℝ} (hx : 0 < x) (hh : 0 ≤ h) :
    ‖drr t h x‖ ≤ (4 + 2 * t * h / x) / x ^ 2 := by
  have hxh : 0 < x + h := by linarith
  set A := Real.exp (-((Real.log x + Real.log (x + h)) / 2)) with hAdef
  set W := V (Real.log x + Real.log (x + h) - 2 * ellT t) with hWdef
  set G := gk (Real.log x + Real.log (x + h) - 2 * ellT t) with hGdef
  have hA1 : A ≤ 1 / x := exp_neg_half_le hx hh
  have hA0 : 0 < A := Real.exp_pos _
  have hW2 : W ≤ 2 := V_le_two _
  have hW0 : 0 ≤ W := V_nonneg _
  have hG1 : G ≤ 1 := by
    rw [hGdef]; unfold gk
    rw [div_le_one (Real.sqrt_pos.mpr Real.pi_pos)]
    calc Real.exp (-(_ ^ 2) / 4) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (Real.log x + Real.log (x + h) - 2 * ellT t)])
      _ ≤ Real.sqrt Real.pi := by
          rw [Real.one_le_sqrt]; linarith [Real.pi_gt_three]
  have hG0 : 0 ≤ G := (gk_pos _).le
  have hinv : 1 / x + 1 / (x + h) ≤ 2 / x := by
    have : 1 / (x + h) ≤ 1 / x := one_div_le_one_div_of_le hx (by linarith)
    have e : 2 / x = 1 / x + 1 / x := by ring
    linarith
  have hinv0 : 0 ≤ 1 / x + 1 / (x + h) := by positivity
  have hdiff : |1 / (x + h) - 1 / x| ≤ h / x ^ 2 := by
    rw [abs_sub_comm, abs_of_nonneg (by
      have : 1 / (x + h) ≤ 1 / x := one_div_le_one_div_of_le hx (by linarith)
      linarith)]
    rw [div_sub_div _ _ hx.ne' hxh.ne', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hh hh) hx.le]
  unfold drr
  rw [← hAdef, ← hWdef, ← hGdef]
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_exp, Real.norm_eq_abs, abs_of_pos hA0]
  have he : (t * I * ((Real.log (x + h) - Real.log x : ℝ) : ℂ)).re = 0 := by simp
  rw [he, Real.exp_zero, mul_one]
  have hb : ‖((-(1 / x + 1 / (x + h)) / 2 : ℝ) : ℂ) * (W : ℂ) + t * I * ((1 / (x + h) - 1 / x : ℝ) : ℂ) * (W : ℂ) +
      ((-G * (1 / x + 1 / (x + h)) : ℝ) : ℂ)‖ ≤ (1 / x) * 2 + t * (h / x ^ 2) * 2 + 1 * (2 / x) := by
    refine (norm_add₃_le).trans ?_
    rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
      Complex.norm_real, norm_I, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht, abs_of_nonneg hW0]
    have e1 : |(-(1 / x + 1 / (x + h)) / 2)| ≤ 1 / x := by
      rw [abs_div, abs_neg, abs_of_nonneg hinv0, abs_two]
      have e : 2 / x = 2 * (1 / x) := by ring
      linarith
    have e3 : |-G * (1 / x + 1 / (x + h))| ≤ 1 * (2 / x) := by
      rw [abs_mul, abs_neg, abs_of_nonneg hG0, abs_of_nonneg hinv0]; gcongr
    have := abs_nonneg (1 / (x + h) - 1 / x)
    gcongr
    · linarith
  calc A * ‖_‖ ≤ (1 / x) * ((1 / x) * 2 + t * (h / x ^ 2) * 2 + 1 * (2 / x)) := by
        gcongr
    _ = (4 + 2 * t * h / x) / x ^ 2 := by field_simp; ring

lemma norm_rr_sub_le (t : ℝ) (ht : 0 ≤ t) {h M : ℝ} (hM : 0 < M) (hh : 0 ≤ h) :
    ‖rr t h (M + 1) - rr t h M‖ ≤ (4 + 2 * t * h / M) / M ^ 2 := by
  have hd : ∀ x ∈ Icc M (M + 1), HasDerivWithinAt (rr t h) (drr t h x) (Icc M (M + 1)) x :=
    fun x hx => (hasDerivAt_rr t (hM.trans_le hx.1) hh).hasDerivWithinAt
  have hb : ∀ x ∈ Ico M (M + 1), ‖drr t h x‖ ≤ (4 + 2 * t * h / M) / M ^ 2 := by
    intro x hx
    have hx0 : 0 < x := hM.trans_le hx.1
    refine (norm_drr_le t ht hx0 hh).trans ?_
    have h1 : 2 * t * h / x ≤ 2 * t * h / M := by
      apply div_le_div_of_nonneg_left (by positivity) hM hx.1
    have h2 : M ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hM.le hx.1 2
    calc (4 + 2 * t * h / x) / x ^ 2 ≤ (4 + 2 * t * h / M) / x ^ 2 := by gcongr
      _ ≤ (4 + 2 * t * h / M) / M ^ 2 := by gcongr
  have := norm_image_sub_le_of_norm_deriv_le_segment' hd hb (M + 1) ⟨by linarith, le_rfl⟩
  simpa using this

/-- Discrete Abel summation. -/
lemma abel_sum (A : ℕ → ℝ) (r : ℕ → ℂ) (a k : ℕ) :
    ∑ M ∈ Ico (a + 1) (a + 1 + k), ((A M - A (M - 1) : ℝ) : ℂ) * r M =
      (A (a + k) : ℂ) * r (a + k + 1) - (A a : ℂ) * r (a + 1) -
        ∑ M ∈ Ico (a + 1) (a + 1 + k), (A M : ℂ) * (r (M + 1) - r M) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show a + 1 + (k + 1) = (a + 1 + k) + 1 by ring, Finset.sum_Ico_succ_top (by omega),
      Finset.sum_Ico_succ_top (by omega), ih]
    rw [show a + 1 + k - 1 = a + k by omega, show a + (k + 1) = a + 1 + k by ring,
      show a + 1 + k + 1 = a + k + 1 + 1 by ring, show a + k + 1 = a + 1 + k by ring]
    push_cast
    ring

lemma shiftSum_succ (h M : ℕ) : shiftSum h (M + 1) - shiftSum h M = lam (M + 1) * lam (M + 1 + h) := by
  unfold shiftSum; rw [Finset.sum_Icc_succ_top (by omega)]; ring

end RamanujanTau.GoodSecondTerm2

namespace RamanujanTau.GoodSecondTerm2

open Complex MeasureTheory Set Filter Topology Finset
open RamanujanTau.ZetaAFE RamanujanTau.GoodSecondTerm RamanujanTau.SubconvexityCond

lemma scs21 : ∃ C : ℝ, 0 ≤ C ∧ ∀ h N : ℕ, 1 ≤ h →
    |shiftSum h N| ≤ C * ((N : ℝ) + h) ^ (1 - 1 / 21 : ℝ) * (h : ℝ) ^ (1 / 21 : ℝ) :=
  (SCSSharp2.shiftedConvolutionBound_sharp2).bound

/-- `Z₄₃ = Σ n^{−43/42}`. -/
noncomputable def Z43 : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-(43 / 42 : ℝ))

lemma Z43_nonneg : 0 ≤ Z43 := tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _

lemma sum_rpow_le_Z43 (s : Finset ℕ) : ∑ n ∈ s, (n : ℝ) ^ (-(43 / 42 : ℝ)) ≤ Z43 :=
  (summable_rpow_nat (p := 43 / 42) (by norm_num)).sum_le_tsum s
    (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

lemma pow2021_le {M h : ℝ} (hM : 1 ≤ M) (hh : 0 ≤ h) (hhM : h ≤ M) :
    (M + h) ^ (1 - 1 / 21 : ℝ) ≤ 2 * M ^ (1 - 1 / 21 : ℝ) := by
  calc (M + h) ^ (1 - 1 / 21 : ℝ) ≤ (2 * M) ^ (1 - 1 / 21 : ℝ) :=
        Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
    _ = 2 ^ (1 - 1 / 21 : ℝ) * M ^ (1 - 1 / 21 : ℝ) := Real.mul_rpow (by norm_num) (by linarith)
    _ ≤ 2 * M ^ (1 - 1 / 21 : ℝ) := by
        gcongr
        calc (2 : ℝ) ^ (1 - 1 / 21 : ℝ) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one 2

/-- `M^{20/21} (4 + 2th/M)/M² ≤ (4 a^{−1/42} + 2th a^{−1−1/42}) M^{−43/42}` for `M ≥ a ≥ 1`. -/
lemma term_le {M a t h : ℝ} (ha : 1 ≤ a) (haM : a ≤ M) (ht : 0 ≤ t) (hh : 0 ≤ h) :
    M ^ (1 - 1 / 21 : ℝ) * ((4 + 2 * t * h / M) / M ^ 2) ≤
      (4 * a ^ (-(1 / 42 : ℝ)) + 2 * t * h * a ^ (-(1 + 1 / 42 : ℝ))) * M ^ (-(43 / 42 : ℝ)) := by
  have hM : 0 < M := by linarith
  have q2 : 1 / M ^ 2 = M ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hM.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div]
  have q3 : 1 / M ^ 3 = M ^ (-(3 : ℝ)) := by
    rw [Real.rpow_neg hM.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div]
  have e1 : M ^ (1 - 1 / 21 : ℝ) * (1 / M ^ 2) = M ^ (-(1 / 42 : ℝ)) * M ^ (-(43 / 42 : ℝ)) := by
    rw [q2, ← Real.rpow_add hM, ← Real.rpow_add hM]; norm_num
  have e2 : M ^ (1 - 1 / 21 : ℝ) * (1 / M ^ 3) = M ^ (-(1 + 1 / 42 : ℝ)) * M ^ (-(43 / 42 : ℝ)) := by
    rw [q3, ← Real.rpow_add hM, ← Real.rpow_add hM]; norm_num
  have h1 : M ^ (-(1 / 42 : ℝ)) ≤ a ^ (-(1 / 42 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) haM (by norm_num)
  have h2 : M ^ (-(1 + 1 / 42 : ℝ)) ≤ a ^ (-(1 + 1 / 42 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) haM (by norm_num)
  have hsplit : M ^ (1 - 1 / 21 : ℝ) * ((4 + 2 * t * h / M) / M ^ 2) =
      4 * (M ^ (1 - 1 / 21 : ℝ) * (1 / M ^ 2)) + 2 * t * h * (M ^ (1 - 1 / 21 : ℝ) * (1 / M ^ 3)) := by
    field_simp
  rw [hsplit, e1, e2]
  have hz : 0 ≤ M ^ (-(43 / 42 : ℝ)) := Real.rpow_nonneg hM.le _
  have hth : 0 ≤ 2 * t * h := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h1 hz, mul_le_mul_of_nonneg_right h2 hz]

/-- **SCS + Abel, partial sums.** -/
theorem scs_partial : ∃ K : ℝ, 0 ≤ K ∧ ∀ (h a k : ℕ) (t : ℝ), 1 ≤ h → h ≤ a → 0 ≤ t →
    ‖∑ M ∈ Finset.Ico (a + 1) (a + 1 + k), ((lam M * lam (M + h) : ℝ) : ℂ) * rr t h M‖ ≤
      K * (h : ℝ) ^ (1 / 21 : ℝ) * ((a : ℝ) ^ (-(1 / 42 : ℝ)) + t * h * (a : ℝ) ^ (-(1 + 1 / 42 : ℝ))) := by
  obtain ⟨C, hC0, hC⟩ := scs21
  refine ⟨C * (8 + 8 * Z43 + 4 * Z43), by have := Z43_nonneg; positivity, fun h a k t hh hha ht => ?_⟩
  have ha1 : 1 ≤ a := hh.trans hha
  have har : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  have hhr : (h : ℝ) ≤ a := by exact_mod_cast hha
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
  set B : ℝ := (h : ℝ) ^ (1 / 21 : ℝ) with hB
  have hB0 : 0 ≤ B := by positivity
  set A : ℕ → ℝ := fun N => shiftSum h N with hA
  have hterm : ∀ M ∈ Finset.Ico (a + 1) (a + 1 + k), ((lam M * lam (M + h) : ℝ) : ℂ) * rr t h M =
      ((A M - A (M - 1) : ℝ) : ℂ) * rr t h M := by
    intro M hM
    simp only [Finset.mem_Ico] at hM
    obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
    simp only [hA, Nat.add_sub_cancel]
    rw [shiftSum_succ]
  rw [Finset.sum_congr rfl hterm, abel_sum A (fun M => rr t h M) a k]
  -- generic bound |A N| ‖r‖
  have hAb : ∀ N : ℕ, a ≤ N → |A N| ≤ 2 * C * (N : ℝ) ^ (1 - 1 / 21 : ℝ) * B := by
    intro N hN
    have hNr : (a : ℝ) ≤ N := by exact_mod_cast hN
    have := hC h N hh
    have hp := pow2021_le (M := N) (h := h) (har.trans hNr) hh0 (hhr.trans hNr)
    calc |A N| ≤ C * ((N : ℝ) + h) ^ (1 - 1 / 21 : ℝ) * B := this
      _ ≤ C * (2 * (N : ℝ) ^ (1 - 1 / 21 : ℝ)) * B := by gcongr
      _ = _ := by ring
  have hbd1 : ∀ N : ℕ, a ≤ N → ‖(A N : ℂ) * rr t h (((N + 1 : ℕ) : ℝ))‖ ≤ 4 * C * B * (a : ℝ) ^ (-(1 / 42 : ℝ)) := by
    intro N hN
    have hNr : (a : ℝ) ≤ N := by exact_mod_cast hN
    have hN1 : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hr := norm_rr_le t hN1 hh0
    have hN0 : (0 : ℝ) < N := by linarith
    calc |A N| * ‖rr t h (((N + 1 : ℕ) : ℝ))‖ ≤ (2 * C * (N : ℝ) ^ (1 - 1 / 21 : ℝ) * B) * (2 / ((N + 1 : ℕ) : ℝ)) := by
          gcongr; exact hAb N hN
      _ ≤ (2 * C * (N : ℝ) ^ (1 - 1 / 21 : ℝ) * B) * (2 / N) := by
          gcongr; push_cast; linarith
      _ = 4 * C * B * ((N : ℝ) ^ (1 - 1 / 21 : ℝ) / N) := by ring
      _ ≤ 4 * C * B * (a : ℝ) ^ (-(1 / 42 : ℝ)) := by
          gcongr
          rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hN0]
          calc (N : ℝ) ^ (1 - 1 / 21 + -1 : ℝ) ≤ (N : ℝ) ^ (-(1 / 42 : ℝ)) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
            _ ≤ (a : ℝ) ^ (-(1 / 42 : ℝ)) := Real.rpow_le_rpow_of_nonpos (by linarith) hNr (by norm_num)
  have hb1 := hbd1 (a + k) (by omega)
  have hb2 := hbd1 a le_rfl
  push_cast at hb1 hb2
  have hsum : ‖∑ M ∈ Finset.Ico (a + 1) (a + 1 + k), (A M : ℂ) * (rr t h (M + 1 : ℕ) - rr t h M)‖ ≤
      2 * C * B * (4 * (a : ℝ) ^ (-(1 / 42 : ℝ)) + 2 * t * h * (a : ℝ) ^ (-(1 + 1 / 42 : ℝ))) * Z43 := by
    refine (norm_sum_le _ _).trans ?_
    have hle : ∀ M ∈ Finset.Ico (a + 1) (a + 1 + k), ‖(A M : ℂ) * (rr t h (M + 1 : ℕ) - rr t h M)‖ ≤
        2 * C * B * (4 * (a : ℝ) ^ (-(1 / 42 : ℝ)) + 2 * t * h * (a : ℝ) ^ (-(1 + 1 / 42 : ℝ))) *
          (M : ℝ) ^ (-(43 / 42 : ℝ)) := by
      intro M hM
      simp only [Finset.mem_Ico] at hM
      have hMr : (a : ℝ) ≤ M := by exact_mod_cast (by omega : a ≤ M)
      have hM0 : (0 : ℝ) < M := by linarith
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hd := norm_rr_sub_le t ht hM0 hh0
      push_cast
      have htl := term_le (M := M) har hMr ht hh0
      calc |A M| * ‖rr t h ((M : ℝ) + 1) - rr t h M‖ ≤ (2 * C * (M : ℝ) ^ (1 - 1 / 21 : ℝ) * B) *
            ((4 + 2 * t * h / M) / (M : ℝ) ^ 2) := by gcongr; exact hAb M (by omega)
        _ = 2 * C * B * ((M : ℝ) ^ (1 - 1 / 21 : ℝ) * ((4 + 2 * t * h / M) / (M : ℝ) ^ 2)) := by ring
        _ ≤ _ := by
            rw [mul_assoc (2 * C * B)]
            gcongr
    refine (Finset.sum_le_sum hle).trans ?_
    rw [← Finset.mul_sum]
    gcongr
    exact sum_rpow_le_Z43 _
  have hz := Z43_nonneg
  push_cast at hsum
  calc ‖(A (a + k) : ℂ) * rr t h (a + k + 1 : ℕ) - (A a : ℂ) * rr t h (a + 1 : ℕ) -
        ∑ M ∈ Finset.Ico (a + 1) (a + 1 + k), (A M : ℂ) * (rr t h (M + 1 : ℕ) - rr t h M)‖
      ≤ ‖(A (a + k) : ℂ) * rr t h (a + k + 1 : ℕ)‖ + ‖(A a : ℂ) * rr t h (a + 1 : ℕ)‖ +
        ‖∑ M ∈ Finset.Ico (a + 1) (a + 1 + k), (A M : ℂ) * (rr t h (M + 1 : ℕ) - rr t h M)‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr; exact norm_sub_le _ _
    _ ≤ 4 * C * B * (a : ℝ) ^ (-(1 / 42 : ℝ)) + 4 * C * B * (a : ℝ) ^ (-(1 / 42 : ℝ)) +
        2 * C * B * (4 * (a : ℝ) ^ (-(1 / 42 : ℝ)) + 2 * t * h * (a : ℝ) ^ (-(1 + 1 / 42 : ℝ))) * Z43 := by
        push_cast; gcongr
    _ ≤ _ := by
        have h1 : 0 ≤ (a : ℝ) ^ (-(1 / 42 : ℝ)) := by positivity
        have h2 : 0 ≤ t * h * (a : ℝ) ^ (-(1 + 1 / 42 : ℝ)) := by positivity
        have h3 : 0 ≤ C * B := by positivity
        nlinarith [mul_nonneg h3 h1, mul_nonneg h3 h2, mul_nonneg (mul_nonneg h3 h1) hz,
          mul_nonneg (mul_nonneg h3 h2) hz]

end RamanujanTau.GoodSecondTerm2

namespace RamanujanTau.GoodSecondTerm2

open Complex MeasureTheory Set Filter Topology Finset
open RamanujanTau.ZetaAFE RamanujanTau.GoodSecondTerm RamanujanTau.SubconvexityCond

/-- **SCS + Abel, infinite tail.** -/
theorem scs_tsum : ∃ K : ℝ, 0 ≤ K ∧ ∀ (h a : ℕ) (t : ℝ), 1 ≤ h → h ≤ a → 0 ≤ t →
    Summable (fun m : ℕ => ((lam (a + 1 + m) * lam (a + 1 + m + h) : ℝ) : ℂ) * rr t h (a + 1 + m : ℕ)) →
    ‖∑' m : ℕ, ((lam (a + 1 + m) * lam (a + 1 + m + h) : ℝ) : ℂ) * rr t h (a + 1 + m : ℕ)‖ ≤
      K * (h : ℝ) ^ (1 / 21 : ℝ) * ((a : ℝ) ^ (-(1 / 42 : ℝ)) + t * h * (a : ℝ) ^ (-(1 + 1 / 42 : ℝ))) := by
  obtain ⟨K, hK0, hK⟩ := scs_partial
  refine ⟨K, hK0, fun h a t hh hha ht hs => ?_⟩
  have hlim := (hs.hasSum.tendsto_sum_nat).norm
  refine le_of_tendsto hlim (Eventually.of_forall fun k => ?_)
  have e : ∑ m ∈ Finset.range k, ((lam (a + 1 + m) * lam (a + 1 + m + h) : ℝ) : ℂ) * rr t h (a + 1 + m : ℕ) =
      ∑ M ∈ Finset.Ico (a + 1) (a + 1 + k), ((lam M * lam (M + h) : ℝ) : ℂ) * rr t h M := by
    rw [Finset.sum_Ico_eq_sum_range, show a + 1 + k - (a + 1) = k by omega]
  rw [e]
  exact hK h a k t hh hha ht

end RamanujanTau.GoodSecondTerm2
