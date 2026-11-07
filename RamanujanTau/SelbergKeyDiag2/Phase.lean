/-
# M3 step 5a: the phase `U(u,u+v) ≈ (u/2π)^{−iv}`

`phase_U`: `‖U(u,u+v) − e^{−iv log(u/2π)}‖ ≤ C |v|/u` for `u ≥ 2`, `|v| ≤ 1`.
With `h(s) = eG(u+s) e^{−is log u}`, `h' = i(Re ψ(6+i(u+s)) − log u) h` and
`|Re ψ(6+it) − log t| ≤ 58/t` (`HeckeAFE2.norm_digamma_sub_log_le`).  Level 1.
-/
import RamanujanTau.SelbergKeyDiag2.Norm
import RamanujanTau.SelbergKey4.Phase

set_option autoImplicit false

namespace RamanujanTau.SelbergKeyDiag2

open Complex Set RamanujanTau.HeckeAFE RamanujanTau.HeckeAFE2 RamanujanTau.SelbergKey RamanujanTau.SelbergKey4
open scoped Real ComplexConjugate

lemma abs_psR_sub_log_le {t : ℝ} (ht : 1 ≤ t) : |psR t - Real.log t| ≤ 58 / t := by
  have ht0 : 0 < t := by linarith
  have h1 := norm_digamma_sub_log_le (z := 6 + (t : ℂ) * I) (by simp; norm_num)
  have hre : (6 + (t : ℂ) * I).re - 1 + |(6 + (t : ℂ) * I).im| = 5 + |t| := by simp; ring
  rw [hre] at h1
  have h2 : |psR t - (Complex.log (6 + (t : ℂ) * I)).re| ≤ 40 / t := by
    unfold psR
    rw [← Complex.sub_re]
    refine (Complex.abs_re_le_norm _).trans (h1.trans ?_)
    rw [abs_of_pos ht0]
    exact div_le_div_of_nonneg_left (by norm_num) ht0 (by linarith)
  have h3 : (Complex.log (6 + (t : ℂ) * I)).re = Real.log (Real.sqrt (36 + t ^ 2)) := by
    rw [Complex.log_re]; congr 1
    rw [Complex.norm_eq_sqrt_sq_add_sq]; congr 1; simp; ring
  have h4 : 0 ≤ Real.log (Real.sqrt (36 + t ^ 2)) - Real.log t ∧
      Real.log (Real.sqrt (36 + t ^ 2)) - Real.log t ≤ 18 / t := by
    have hs : t ≤ Real.sqrt (36 + t ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
    have hs0 : 0 < Real.sqrt (36 + t ^ 2) := by positivity
    constructor
    · have := Real.log_le_log ht0 hs; linarith
    · rw [← Real.log_div hs0.ne' ht0.ne']
      refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
      have hsq : Real.sqrt (36 + t ^ 2) ≤ t + 18 / t := by
        rw [Real.sqrt_le_left (by positivity)]
        have : (t + 18 / t) ^ 2 = t ^ 2 + 36 + 324 / t ^ 2 := by field_simp; ring
        rw [this]; have : 0 ≤ 324 / t ^ 2 := by positivity
        linarith
      rw [div_sub_one ht0.ne', div_le_div_iff₀ ht0 ht0]
      have e : (t + 18 / t) * t = t ^ 2 + 18 := by field_simp
      have hm := mul_le_mul_of_nonneg_right hsq ht0.le
      rw [e] at hm
      nlinarith
  rw [h3] at h2
  have : |psR t - Real.log t| ≤ |psR t - Real.log (Real.sqrt (36 + t ^ 2))| +
      |Real.log (Real.sqrt (36 + t ^ 2)) - Real.log t| := by
    rw [show psR t - Real.log t = (psR t - Real.log (Real.sqrt (36 + t ^ 2))) +
      (Real.log (Real.sqrt (36 + t ^ 2)) - Real.log t) by ring]
    exact abs_add_le _ _
  refine this.trans ?_
  rw [abs_of_nonneg h4.1]
  have : 40 / t + 18 / t = 58 / t := by ring
  linarith [h4.2]

lemma norm_cexp_negI (x : ℝ) : ‖cexp (-((x : ℝ) : ℂ) * I)‖ = 1 := by
  rw [show -((x : ℝ) : ℂ) * I = ((-x : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma abs_log_shift_le {u s : ℝ} (hu : 2 ≤ u) (hs : |s| ≤ 1) : |Real.log (u + s) - Real.log u| ≤ 2 / u := by
  have hu0 : 0 < u := by linarith
  have hus : u / 2 ≤ u + s := by linarith [(abs_le.1 hs).1]
  have hus0 : 0 < u + s := by linarith
  rw [abs_le]; constructor
  · have := Real.log_le_sub_one_of_pos (show 0 < u / (u + s) by positivity)
    rw [Real.log_div hu0.ne' hus0.ne'] at this
    have h2 : u / (u + s) - 1 ≤ 2 / u := by
      rw [div_sub_one hus0.ne', div_le_div_iff₀ hus0 hu0]; nlinarith [(abs_le.1 hs).1, (abs_le.1 hs).2]
    linarith
  · have := Real.log_le_sub_one_of_pos (show 0 < (u + s) / u by positivity)
    rw [Real.log_div hus0.ne' hu0.ne'] at this
    have h2 : (u + s) / u - 1 ≤ 2 / u := by
      rw [div_sub_one hu0.ne', div_le_div_iff_of_pos_right hu0]; linarith [(abs_le.1 hs).2]
    linarith

/-- **`U(u,u+v) = e^{−iv log(u/2π)} + O(|v|/u)`.** -/
theorem phase_U : ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : ℝ, 2 ≤ u → |v| ≤ 1 →
    ‖Ush u (u + v) - cexp (-((v * Real.log (u / (2 * π)) : ℝ) : ℂ) * I)‖ ≤ C * |v| / u := by
  refine ⟨118, by norm_num, fun u v hu hv => ?_⟩
  have hu0 : 0 < u := by linarith
  set L := Real.log u
  set h : ℝ → ℂ := fun s => eG (u + s) * cexp (-((s * L : ℝ) : ℂ) * I) with hh
  set h' : ℝ → ℂ := fun s => I * ((psR (u + s) - L : ℝ) : ℂ) * h s with hh'
  have hder : ∀ s, HasDerivAt h (h' s) s := by
    intro s
    have h1 := (hasDerivAt_eG (u + s)).scomp s ((hasDerivAt_id s).const_add u)
    have h2 : HasDerivAt (fun s : ℝ => cexp (-((s * L : ℝ) : ℂ) * I))
        (cexp (-((s * L : ℝ) : ℂ) * I) * (-(L : ℂ) * I)) s := by
      have := ((hasDerivAt_id s).mul_const L).ofReal_comp
      have := (this.neg.mul_const I).cexp
      convert this using 1
      simp
    convert h1.mul h2 using 1
    simp only [hh', hh, Function.comp_def, real_smul]
    push_cast; ring
  have hbound : ∀ s ∈ Icc (-1:ℝ) 1, ‖h' s‖ ≤ 118 / u := by
    intro s hs
    have hs1 : |s| ≤ 1 := abs_le.2 ⟨hs.1, hs.2⟩
    have hus : 1 ≤ u + s := by linarith [hs.1]
    simp only [hh', hh]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, norm_eG, one_mul, Complex.norm_real,
      norm_cexp_negI, mul_one, Real.norm_eq_abs]
    have h1 := abs_psR_sub_log_le hus
    have h2 := abs_log_shift_le hu hs1
    have h3 : 58 / (u + s) ≤ 116 / u := by
      rw [div_le_div_iff₀ (by linarith) hu0]; nlinarith [hs.1]
    calc |psR (u + s) - L| ≤ |psR (u + s) - Real.log (u + s)| + |Real.log (u + s) - L| := by
          rw [show psR (u + s) - L = (psR (u + s) - Real.log (u + s)) + (Real.log (u + s) - L) by ring]
          exact abs_add_le _ _
      _ ≤ 116 / u + 2 / u := add_le_add (h1.trans h3) h2
      _ = 118 / u := by ring
  have hmvt := (convex_Icc (-1:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (hder s).hasDerivWithinAt) hbound (show (0:ℝ) ∈ Icc (-1:ℝ) 1 by constructor <;> norm_num)
    (show v ∈ Icc (-1:ℝ) 1 from ⟨(abs_le.1 hv).1, (abs_le.1 hv).2⟩)
  rw [Ush_eq]
  have h2π : (0:ℝ) < 2 * π := by positivity
  have e1 : cexp (-((v * Real.log (u / (2 * π)) : ℝ) : ℂ) * I) =
      (2 * π : ℂ) ^ ((v : ℂ) * I) * cexp (-((v * L : ℝ) : ℂ) * I) := by
    rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, cpow_eq_exp h2π, ← Complex.exp_add,
      Real.log_div hu0.ne' h2π.ne']
    congr 1; push_cast; ring
  have e2 : eG u * conj (eG (u + v)) - cexp (-((v * L : ℝ) : ℂ) * I) =
      conj (eG (u + v)) * (h 0 - h v) := by
    simp only [hh]
    have hc : conj (eG (u + v)) * eG (u + v) = 1 := by
      rw [Complex.conj_mul', norm_eG]; simp
    rw [add_zero, zero_mul, Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero, mul_one,
      mul_sub, ← mul_assoc, hc, one_mul, mul_comm]
  rw [e1, ← mul_sub, e2, norm_mul, norm_mul]
  have hn2π : ‖(2 * π : ℂ) ^ ((v : ℂ) * I)‖ = 1 := by
    rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, norm_ofReal_cpow h2π]; simp
  rw [hn2π, one_mul, Complex.norm_conj, norm_eG, one_mul, norm_sub_rev]
  refine hmvt.trans (le_of_eq ?_)
  rw [sub_zero, Real.norm_eq_abs]; ring

/-- `ψ(6+it)` is `72/(w−1)`-Lipschitz on `[w−1, w+1]`. -/
lemma digamma_lip {w : ℝ} (hw : 3 ≤ w) {t₁ t₂ : ℝ} (h1 : t₁ ∈ Icc (w - 1) (w + 1)) (h2 : t₂ ∈ Icc (w - 1) (w + 1)) :
    ‖digamma (6 + (t₂ : ℂ) * I) - digamma (6 + (t₁ : ℂ) * I)‖ ≤ 72 / (w - 1) * ‖t₂ - t₁‖ := by
  refine (convex_Icc (w - 1) (w + 1)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t : ℝ => digamma (6 + (t : ℂ) * I))
    (fun t _ => (differentiable_digamma_line t).hasDerivWithinAt) (fun t ht => ?_) h1 h2
  have ht1 : w - 1 ≤ t := ht.1
  have hw1 : 0 < w - 1 := by linarith
  have hb := RamanujanTau.HeckeAFE3.norm_iteratedDeriv_digamma_le (k := 1) le_rfl (z := 6 + (t : ℂ) * I) (by simp; norm_num)
  rw [iteratedDeriv_one] at hb
  rw [norm_mul, Complex.norm_I, one_mul]
  refine hb.trans ?_
  have hz : w - 1 ≤ ‖6 + (t : ℂ) * I‖ := by
    have := Complex.abs_im_le_norm (6 + (t : ℂ) * I)
    simp at this
    linarith [le_abs_self t]
  calc (18 * (Nat.factorial 1 : ℕ) * 4 ^ 1 : ℝ) / ‖6 + (t : ℂ) * I‖ ^ 1 = 72 / ‖6 + (t : ℂ) * I‖ := by norm_num
    _ ≤ 72 / (w - 1) := div_le_div_of_nonneg_left (by norm_num) hw1 hz

lemma hasDerivAt_logGl (t : ℝ) :
    HasDerivAt (fun s => Real.log ‖Gl s‖) (-(digamma (6 + t * I)).im) t := by
  have h := (hasDerivAt_normGl t).log (normGl_pos t).ne'
  convert h using 1
  field_simp [(normGl_pos t).ne']

/-- **The pole phase**: `U(u,u+v) G(iv/2) (4π²)^{−iv/2} = 1 + O(v²/u)`. -/
theorem phase_Phi : ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : ℝ, 40 ≤ u → |v| ≤ 1 →
    ‖Ush u (u + v) * Gsh u (u + v) (((v / 2 : ℝ) : ℂ) * I) *
        ((4 * π ^ 2 : ℝ) : ℂ) ^ (-(((v / 2 : ℝ) : ℂ) * I)) - 1‖ ≤ C * v ^ 2 / u := by
  refine ⟨144, by norm_num, fun u v hu hv => ?_⟩
  set h := v / 2 with hhdef
  set w := u + h with hwdef
  clear_value h w
  have hv2 : v = 2 * h := by rw [hhdef]; ring
  have hh1 : |h| ≤ 1 / 2 := by rw [hhdef, abs_div]; norm_num; linarith
  have hw : 39 ≤ w := by linarith [(abs_le.1 hh1).1]
  -- (i) the identity
  have hGw : Gamma (6 + (u : ℂ) * I + ((h : ℝ) : ℂ) * I) = Gl w := by
    unfold Gl; congr 1; rw [hwdef]; push_cast; ring
  have hGw' : Gamma (6 - ((u + v : ℝ) : ℂ) * I + ((h : ℝ) : ℂ) * I) = conj (Gl w) := by
    unfold Gl; rw [← Complex.Gamma_conj]; congr 1
    apply Complex.ext <;> (simp [hwdef]; try linarith)
  have hGc : Gamma (6 - ((u + v : ℝ) : ℂ) * I) = conj (Gl (u + v)) := by
    unfold Gl; rw [← Complex.Gamma_conj]; congr 1; apply Complex.ext <;> simp
  have hne1 : Gl u ≠ 0 := Gl_ne u
  have hne2 : conj (Gl (u + v)) ≠ 0 := by rw [map_ne_zero]; exact Gl_ne (u + v)
  have h2π : (0:ℝ) < 2 * π := by positivity
  have hpow : (2 * π : ℂ) ^ (((u + v - u : ℝ) : ℂ) * I) * ((4 * π ^ 2 : ℝ) : ℂ) ^ (-(((h : ℝ) : ℂ) * I)) = 1 := by
    rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, cpow_eq_exp h2π,
      cpow_eq_exp (by positivity), ← Complex.exp_add,
      show (4 * π ^ 2 : ℝ) = (2 * π) ^ 2 by ring, Real.log_pow, ← Complex.exp_zero]
    congr 1
    have hv2c : (v : ℂ) = 2 * (h : ℂ) := by rw [hv2]; push_cast; ring
    push_cast
    linear_combination (((Real.log (2 * π) : ℝ) : ℂ) * I) * hv2c
  have eU : Ush u (u + v) = (2 * π : ℂ) ^ (((u + v - u : ℝ) : ℂ) * I) * (Gl u * conj (Gl (u + v))) /
      ((‖Gl u‖ * ‖Gl (u + v)‖ : ℝ) : ℂ) := by
    unfold Ush; rw [hGc]; rfl
  have eG' : Gsh u (u + v) (((h : ℝ) : ℂ) * I) = Gl w * conj (Gl w) / (Gl u * conj (Gl (u + v))) := by
    unfold Gsh; rw [hGw, hGw', hGc]; rfl
  have hn' : Gl w * conj (Gl w) = ((‖Gl w‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hPhi : Ush u (u + v) * Gsh u (u + v) (((h : ℝ) : ℂ) * I) * ((4 * π ^ 2 : ℝ) : ℂ) ^ (-(((h : ℝ) : ℂ) * I)) =
      ((‖Gl w‖ ^ 2 / (‖Gl u‖ * ‖Gl (u + v)‖) : ℝ) : ℂ) := by
    rw [eU, eG']
    have hnn : ((‖Gl u‖ * ‖Gl (u + v)‖ : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (mul_pos (normGl_pos u) (normGl_pos (u + v))).ne'
    calc _ = ((2 * π : ℂ) ^ (((u + v - u : ℝ) : ℂ) * I) * ((4 * π ^ 2 : ℝ) : ℂ) ^ (-(((h : ℝ) : ℂ) * I))) *
          (Gl w * conj (Gl w)) / ((‖Gl u‖ * ‖Gl (u + v)‖ : ℝ) : ℂ) := by
          field_simp
      _ = _ := by rw [hpow, hn', one_mul, ← Complex.ofReal_div]
  rw [hPhi]
  -- (ii) the second difference of `log ‖Γ(6+it)‖`
  set F : ℝ → ℝ := fun s => Real.log ‖Gl s‖ with hF
  set k : ℝ → ℝ := fun s => F (w + s) + F (w - s) with hk
  set k' : ℝ → ℝ := fun s => -(digamma (6 + ((w + s : ℝ) : ℂ) * I)).im + (digamma (6 + ((w - s : ℝ) : ℂ) * I)).im
  have hkd : ∀ s, HasDerivAt k (k' s) s := by
    intro s
    have h1 := (hasDerivAt_logGl (w + s)).comp s ((hasDerivAt_id s).const_add w)
    have h2 := (hasDerivAt_logGl (w - s)).comp s ((hasDerivAt_id s).const_sub w)
    convert h1.add h2 using 1
    simp only [k']; ring
  have hkb : ∀ s ∈ uIcc (0:ℝ) h, ‖k' s‖ ≤ 144 * |h| / (w - 1) := by
    intro s hs
    have hsh : |s| ≤ |h| := by
      rcases le_total 0 h with h0 | h0
      · rw [uIcc_of_le h0] at hs; rw [abs_of_nonneg hs.1, abs_of_nonneg h0]; exact hs.2
      · rw [uIcc_of_ge h0] at hs; rw [abs_of_nonpos hs.2, abs_of_nonpos h0]; linarith [hs.1]
    have hs1 : |s| ≤ 1 := hsh.trans (by linarith)
    have hm1 : w + s ∈ Icc (w - 1) (w + 1) := ⟨by linarith [(abs_le.1 hs1).1], by linarith [(abs_le.1 hs1).2]⟩
    have hm2 : w - s ∈ Icc (w - 1) (w + 1) := ⟨by linarith [(abs_le.1 hs1).2], by linarith [(abs_le.1 hs1).1]⟩
    have hl := digamma_lip (by linarith) hm1 hm2
    simp only [k']
    rw [Real.norm_eq_abs, show -(digamma (6 + ((w + s : ℝ) : ℂ) * I)).im + (digamma (6 + ((w - s : ℝ) : ℂ) * I)).im =
      (digamma (6 + ((w - s : ℝ) : ℂ) * I) - digamma (6 + ((w + s : ℝ) : ℂ) * I)).im by rw [Complex.sub_im]; ring]
    refine (Complex.abs_im_le_norm _).trans (hl.trans ?_)
    rw [Real.norm_eq_abs, show w - s - (w + s) = -(2 * s) by ring, abs_neg, abs_mul, abs_two]
    have hw1 : 0 < w - 1 := by linarith
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hw1]
    nlinarith [abs_nonneg s]
  have hmvt := (convex_uIcc (0:ℝ) h).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (hkd s).hasDerivWithinAt) hkb left_mem_uIcc right_mem_uIcc
  rw [sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  -- the real quantity
  have hpos : ∀ s, 0 < ‖Gl s‖ := normGl_pos
  have hu' : u = w - h := by rw [hwdef]; ring
  have huv : u + v = w + h := by rw [hwdef, hv2]; ring
  have hexp : ‖Gl w‖ ^ 2 / (‖Gl u‖ * ‖Gl (u + v)‖) = Real.exp (k 0 - k h) := by
    simp only [hk, hF, add_zero, sub_zero]
    rw [Real.exp_sub, Real.exp_add, Real.exp_add, Real.exp_log (hpos _), Real.exp_log (hpos _),
      Real.exp_log (hpos _), huv, hu']
    ring
  rw [hexp]
  set x := k 0 - k h
  have hx : |x| ≤ 144 * |h| / (w - 1) * |h| := by
    simp only [x]; rw [abs_sub_comm]; exact hmvt
  have hw1 : 38 ≤ w - 1 := by linarith
  have hx1 : |x| ≤ 1 := by
    refine hx.trans ?_
    rw [div_mul_eq_mul_div, div_le_one (by linarith)]
    nlinarith [abs_nonneg h]
  have he := Real.abs_exp_sub_one_le hx1
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  refine he.trans ?_
  have hh2 : |h| ^ 2 = v ^ 2 / 4 := by rw [sq_abs, hv2]; ring
  calc 2 * |x| ≤ 2 * (144 * |h| / (w - 1) * |h|) := by linarith
    _ = 72 * v ^ 2 / (w - 1) := by
        rw [show 144 * |h| / (w - 1) * |h| = 144 * |h| ^ 2 / (w - 1) by ring, hh2]; ring
    _ ≤ 144 * v ^ 2 / u := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith [sq_nonneg v, (abs_le.1 hh1).1]

end RamanujanTau.SelbergKeyDiag2
