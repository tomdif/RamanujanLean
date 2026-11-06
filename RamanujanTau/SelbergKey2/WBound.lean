/-
# M1(b): uniform bounds for the lag weight `W̃_{u,u'}(ξ)`

`W̃_{u,u'}(ξ) = (1/2πi)∫_{(2)} [Γ(6+iu+z)Γ(6−iu'+z)/(Γ(6+iu)Γ(6−iu'))] ξ^{−z} e^{z²} dz/z`
(`ShiftAFE.Wsh`).  With `T(t) = ‖3/2 + it‖ ≍ 1+|t|`:

* `W2sh_shift`: the line `Re z = c > 0` may be moved freely;
* `W2sh_residue`: crossing `z = 0` picks up `Γ(a)Γ(b)`;
* `W2sh_line_bound`: on `Re z = x` (`x ≥ −9/2`, `x ≠ 0`),
  `|W(6+iu, 6−iu'; ξ)| ≤ K_x (T(u)T(u')/ξ)^x |Γ(6+iu)||Γ(6+iu')|`;
* **`Wsh_decay`**: `|W̃_{u,u'}(ξ)| ≤ C_A (T(u)T(u')/ξ)^A` for every `A > 0`;
* **`Wsh_sub_one`**: `|W̃_{u,u'}(ξ) − 1| ≤ C_c (ξ/(T(u)T(u')))^c` for `0 < c ≤ 9/2`;
* **`Wsh_bound`**: `|W̃_{u,u'}(ξ)| ≤ C_A (1 + ξ/(T(u)T(u')))^{−A}` for every `A ≥ 0`.
All constants are uniform in `u, u' ∈ ℝ`, `ξ > 0` (in particular uniform in the lag `v = u'−u`).
Level 1.
-/
import RamanujanTau.SelbergKey2.Cont

set_option autoImplicit false

namespace RamanujanTau.SelbergKey2

open Complex MeasureTheory Set Filter Topology RamanujanTau.HeckeL RamanujanTau.HeckeAFE
open RamanujanTau.SelbergKey
open scoped Real ComplexConjugate

lemma differentiableOn_W2sh_integrand {a b : ℂ} {ξ c₁ c₂ : ℝ} (hξ : 0 < ξ) (ha : 0 < a.re + c₁)
    (hb : 0 < b.re + c₁) (h0 : (0:ℂ) ∉ strip c₁ c₂) :
    DifferentiableOn ℂ (fun z => Gamma (a + z) * Gamma (b + z) * (ξ : ℂ) ^ (-z) * cexp (z ^ 2) / z)
      (strip c₁ c₂) := by
  have hξ0 : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ.ne'
  refine DifferentiableOn.div ?_ differentiableOn_id (fun u hu h' => h0 (h' ▸ hu))
  refine (((differentiableOn_Gamma_add ha).mul (differentiableOn_Gamma_add hb)).mul ?_).mul ?_
  · exact (differentiable_neg.const_cpow (Or.inl hξ0)).differentiableOn
  · exact (Complex.differentiable_exp.comp (differentiable_pow 2)).differentiableOn

/-- The line `Re z = c > 0` of `W(a,b;ξ)` may be moved. -/
theorem W2sh_shift {a b : ℂ} {ξ c₁ c₂ : ℝ} (hξ : 0 < ξ) (hc₁ : 0 < c₁) (h12 : c₁ ≤ c₂)
    (ha : 0 < a.re + c₁) (hb : 0 < b.re + c₁) : W2sh a b ξ c₁ = W2sh a b ξ c₂ := by
  unfold W2sh
  congr 1
  obtain ⟨M₁, hM₁⟩ := gamma_bdd_strip h12 ha
  obtain ⟨M₂, hM₂⟩ := gamma_bdd_strip h12 hb
  refine vline_shift h12 (differentiableOn_W2sh_integrand hξ ha hb ?_) ?_
  · intro h; have := h.1; simp at this; linarith
  · refine ⟨|M₁| * |M₂| * (ξ ^ (-c₂) + ξ ^ (-c₁)) * Real.exp (c₂ ^ 2) * c₁⁻¹, fun x y hx1 hx2 => ?_⟩
    have hmem := mem_strip_line hx1 hx2 y
    have hG₁ := (hM₁ _ hmem).trans (le_abs_self M₁)
    have hG₂ := (hM₂ _ hmem).trans (le_abs_self M₂)
    show ‖Gamma (a + ((x : ℂ) + y * I)) * Gamma (b + ((x : ℂ) + y * I)) *
      (ξ : ℂ) ^ (-((x : ℂ) + y * I)) * cexp (((x : ℂ) + y * I) ^ 2) / ((x : ℂ) + y * I)‖ ≤
      |M₁| * |M₂| * (ξ ^ (-c₂) + ξ ^ (-c₁)) * Real.exp (c₂ ^ 2) * c₁⁻¹ * Real.exp (-(1 / 2) * y ^ 2)
    rw [div_eq_mul_inv, norm_mul, norm_mul, norm_mul, norm_mul, norm_ofReal_cpow hξ, norm_cexp_sq]
    have hr : (-((x : ℂ) + y * I)).re = -x := by simp
    rw [hr]
    have h1 := rpow_le_add_of_mem hξ (neg_le_neg hx2) (neg_le_neg hx1)
    have h2 : Real.exp (x ^ 2 - y ^ 2) ≤ Real.exp (c₂ ^ 2) * Real.exp (-(1 / 2) * y ^ 2) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith [sq_nonneg y]
    have h3 : ‖((x : ℂ) + y * I)⁻¹‖ ≤ c₁⁻¹ :=
      (norm_inv_line_le (by linarith) y).trans (inv_anti₀ hc₁ hx1)
    calc ‖Gamma (a + (↑x + ↑y * I))‖ * ‖Gamma (b + (↑x + ↑y * I))‖ * ξ ^ (-x) *
          Real.exp (x ^ 2 - y ^ 2) * ‖((x : ℂ) + y * I)⁻¹‖
        ≤ |M₁| * |M₂| * (ξ ^ (-c₂) + ξ ^ (-c₁)) * (Real.exp (c₂ ^ 2) * Real.exp (-(1 / 2) * y ^ 2)) *
          c₁⁻¹ := by gcongr
      _ = _ := by ring

/-- **Crossing the pole**: `W(a,b;ξ)|_{c} − W(a,b;ξ)|_{−c'} = Γ(a)Γ(b)`, `0 < c' < Re a, Re b`. -/
theorem W2sh_residue {a b : ℂ} {ξ c c' : ℝ} (hξ : 0 < ξ) (hc : 0 < c) (hc' : 0 < c')
    (ha : c' < a.re) (hb : c' < b.re) : W2sh a b ξ c - W2sh a b ξ (-c') = Gamma a * Gamma b := by
  have hξ0 : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ.ne'
  have h0a : 0 < a.re + -c' := by linarith
  have h0b : 0 < b.re + -c' := by linarith
  obtain ⟨M₁, hM₁⟩ := gamma_bdd_strip (by linarith : -c' ≤ c) h0a
  obtain ⟨M₂, hM₂⟩ := gamma_bdd_strip (by linarith : -c' ≤ c) h0b
  have hF : DifferentiableOn ℂ (fun z => Gamma (a + z) * Gamma (b + z) * (ξ : ℂ) ^ (-z))
      (strip (-c') c) :=
    ((differentiableOn_Gamma_add h0a).mul (differentiableOn_Gamma_add h0b)).mul
      (differentiable_neg.const_cpow (Or.inl hξ0)).differentiableOn
  have hFb : ∃ M', ∀ z ∈ strip (-c') c, ‖Gamma (a + z) * Gamma (b + z) * (ξ : ℂ) ^ (-z)‖ ≤ M' := by
    refine ⟨M₁ * M₂ * (ξ ^ (-c) + ξ ^ c'), fun z hz => ?_⟩
    rw [norm_mul, norm_mul, norm_ofReal_cpow hξ]
    have hG₁ := hM₁ z hz
    have hG₂ := hM₂ z hz
    have h1 := rpow_le_add_of_mem hξ (a := -c) (b := c') (x := (-z).re)
      (by simp; linarith [hz.2]) (by simp; linarith [hz.1])
    have hM0 : 0 ≤ M₁ := le_trans (norm_nonneg _) hG₁
    exact mul_le_mul (mul_le_mul hG₁ hG₂ (norm_nonneg _) hM0) h1 (by positivity)
      (mul_nonneg hM0 (le_trans (norm_nonneg _) hG₂))
  have hres := vline_residue (by linarith : -c' < 0) hc hF hFb
  unfold W2sh
  rw [← mul_sub]
  have e : (fun z => Gamma (a + z) * Gamma (b + z) * (ξ : ℂ) ^ (-z) * cexp (z ^ 2) / z) =
      (fun z => (Gamma (a + z) * Gamma (b + z) * (ξ : ℂ) ^ (-z)) * cexp (z ^ 2) / z) := rfl
  rw [e, hres]
  simp only [add_zero, neg_zero, cpow_zero, mul_one]
  field_simp [two_pi_ne_zero]

lemma Tq_neg (t : ℝ) : Tq (-t) = Tq t := by
  unfold Tq
  have : ((3 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I) = conj ((3 / 2 : ℂ) + (t : ℂ) * I) := by
    apply Complex.ext <;> simp [map_ofNat, map_div₀]
  rw [this, Complex.norm_conj]

lemma poly_exp_bound2 {q : ℝ} (hq : 0 ≤ q) (y : ℝ) :
    (1 + |y|) ^ q * Real.exp (π * |y|) * Real.exp (-1 * y ^ 2) ≤
      Real.exp ((q + π) ^ 2 / 2) * Real.exp (-(1 / 2) * y ^ 2) := by
  have h1 : (1 + |y|) ^ q ≤ Real.exp (q * |y|) := by
    rw [mul_comm, Real.exp_mul]
    exact Real.rpow_le_rpow (by positivity) (by linarith [Real.add_one_le_exp |y|]) hq
  calc (1 + |y|) ^ q * Real.exp (π * |y|) * Real.exp (-1 * y ^ 2)
      ≤ Real.exp (q * |y|) * Real.exp (π * |y|) * Real.exp (-1 * y ^ 2) := by gcongr
    _ = Real.exp ((q + π) * |y| - y ^ 2) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp ((q + π) ^ 2 / 2 + -(1 / 2) * y ^ 2) := by
        apply Real.exp_le_exp.2
        nlinarith [sq_nonneg (|y| - (q + π)), sq_abs y]
    _ = _ := by rw [Real.exp_add]

/-- **Bound on a single line** `Re z = x` (`x ≥ −9/2`, `x ≠ 0`), uniform in `u, u', ξ`. -/
theorem W2sh_line_bound {x : ℝ} (hx : -9 / 2 ≤ x) (hx0 : x ≠ 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u u' ξ : ℝ, 0 < ξ →
      ‖W2sh (6 + u * I) (6 - u' * I) ξ x‖ ≤
        K * (Tq u * Tq u' / ξ) ^ x * (‖Gamma (6 + u * I)‖ * ‖Gamma (6 + u' * I)‖) := by
  obtain ⟨C, hC0, hC⟩ := norm_Gamma_ratio_line hx
  have hp0 : 0 ≤ 2 * (11 / 2 + x) := by linarith
  set E : ℝ := Real.exp ((2 * (11 / 2 + x) + π) ^ 2 / 2)
  set J : ℝ := ∫ y : ℝ, Real.exp (-(1 / 2) * y ^ 2)
  have hJ : 0 ≤ J := integral_nonneg fun _ => (Real.exp_pos _).le
  have hx' : 0 < |x| := abs_pos.2 hx0
  set K : ℝ := (2 * π)⁻¹ * (C * C * E * Real.exp (x ^ 2) * |x|⁻¹ * J)
  refine ⟨K, by positivity, fun u u' ξ hξ => ?_⟩
  set G : ℝ := ‖Gamma (6 + u * I)‖ * ‖Gamma (6 + u' * I)‖
  have hG0 : 0 ≤ G := by positivity
  set B : ℝ := C * C * (Tq u * Tq u') ^ x * G * ξ ^ (-x) * Real.exp (x ^ 2) * |x|⁻¹ * E
  have hB : ∀ y : ℝ, ‖Gamma ((6 + u * I) + ((x : ℂ) + y * I)) *
      Gamma ((6 - u' * I) + ((x : ℂ) + y * I)) * (ξ : ℂ) ^ (-((x : ℂ) + y * I)) *
      cexp (((x : ℂ) + y * I) ^ 2) / ((x : ℂ) + y * I)‖ ≤ B * Real.exp (-(1 / 2) * y ^ 2) := by
    intro y
    rw [div_eq_mul_inv, norm_mul, norm_mul, norm_mul, norm_mul, norm_ofReal_cpow hξ, norm_cexp_sq]
    have hr : (-((x : ℂ) + y * I)).re = -x := by simp
    rw [hr]
    have hi : ‖((x : ℂ) + y * I)⁻¹‖ ≤ |x|⁻¹ := by
      rw [norm_inv]; exact inv_anti₀ hx' (norm_line_ge y)
    have he : Real.exp (x ^ 2 - y ^ 2) = Real.exp (x ^ 2) * Real.exp (-1 * y ^ 2) := by
      rw [← Real.exp_add]; ring_nf
    rw [he]
    have h1 := hC u y
    have h2 : ‖Gamma ((6 - u' * I) + ((x : ℂ) + y * I))‖ ≤
        C * Tq u' ^ x * ((1 + |y|) ^ (11 / 2 + x) * Real.exp (π * |y| / 2)) *
          ‖Gamma (6 + u' * I)‖ := by
      have := hC (-u') y
      rw [Tq_neg, show (6 + ((-u' : ℝ) : ℂ) * I) = 6 - u' * I by push_cast; ring,
        norm_Gamma_six_sub] at this
      exact this
    have hpe := poly_exp_bound2 hp0 y
    have hTx : 0 ≤ Tq u ^ x := (Real.rpow_pos_of_pos (Tq_pos u) _).le
    have hTx' : 0 ≤ Tq u' ^ x := (Real.rpow_pos_of_pos (Tq_pos u') _).le
    have hξx : 0 ≤ ξ ^ (-x) := (Real.rpow_pos_of_pos hξ _).le
    have hsq : ((1 + |y|) ^ (11 / 2 + x) * Real.exp (π * |y| / 2)) *
        ((1 + |y|) ^ (11 / 2 + x) * Real.exp (π * |y| / 2)) =
        (1 + |y|) ^ (2 * (11 / 2 + x)) * Real.exp (π * |y|) := by
      have ea : Real.exp (π * |y|) = Real.exp (π * |y| / 2) * Real.exp (π * |y| / 2) := by
        rw [← Real.exp_add]; ring_nf
      have eb : (1 + |y|) ^ (2 * (11 / 2 + x)) = (1 + |y|) ^ (11 / 2 + x) * (1 + |y|) ^ (11 / 2 + x) := by
        rw [← Real.rpow_add (by positivity)]; ring_nf
      rw [ea, eb]; ring
    have hTT : (Tq u * Tq u') ^ x = Tq u ^ x * Tq u' ^ x :=
      Real.mul_rpow (Tq_pos u).le (Tq_pos u').le
    have hy0 : 0 ≤ (1 + |y|) ^ (11 / 2 + x) * Real.exp (π * |y| / 2) := by positivity
    calc ‖Gamma (6 + ↑u * I + (↑x + ↑y * I))‖ * ‖Gamma (6 - ↑u' * I + (↑x + ↑y * I))‖ * ξ ^ (-x) *
          (Real.exp (x ^ 2) * Real.exp (-1 * y ^ 2)) * ‖((x : ℂ) + y * I)⁻¹‖
        ≤ (C * Tq u ^ x * ((1 + |y|) ^ (11 / 2 + x) * Real.exp (π * |y| / 2)) *
            ‖Gamma (6 + u * I)‖) *
          (C * Tq u' ^ x * ((1 + |y|) ^ (11 / 2 + x) * Real.exp (π * |y| / 2)) *
            ‖Gamma (6 + u' * I)‖) * ξ ^ (-x) *
          (Real.exp (x ^ 2) * Real.exp (-1 * y ^ 2)) * |x|⁻¹ := by
          gcongr
      _ = C * C * (Tq u * Tq u') ^ x * G * ξ ^ (-x) * Real.exp (x ^ 2) * |x|⁻¹ *
          ((1 + |y|) ^ (2 * (11 / 2 + x)) * Real.exp (π * |y|) * Real.exp (-1 * y ^ 2)) := by
          rw [hTT, ← hsq]; simp only [G]; ring
      _ ≤ C * C * (Tq u * Tq u') ^ x * G * ξ ^ (-x) * Real.exp (x ^ 2) * |x|⁻¹ *
          (E * Real.exp (-(1 / 2) * y ^ 2)) := by
          have : 0 ≤ C * C * (Tq u * Tq u') ^ x * G * ξ ^ (-x) * Real.exp (x ^ 2) * |x|⁻¹ := by
            have := Real.rpow_nonneg (mul_nonneg (Tq_pos u).le (Tq_pos u').le) x
            positivity
          exact mul_le_mul_of_nonneg_left hpe this
      _ = _ := by ring
  have hint := (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1 / 2)).const_mul B
  have hI := norm_integral_le_of_norm_le hint (Eventually.of_forall hB)
  rw [integral_const_mul] at hI
  unfold W2sh vline
  rw [norm_mul]
  have h2pi : ‖(2 * π : ℂ)⁻¹‖ = (2 * π)⁻¹ := by
    rw [norm_inv, show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  rw [h2pi]
  have hdiv : (Tq u * Tq u' / ξ) ^ x = (Tq u * Tq u') ^ x * ξ ^ (-x) := by
    rw [Real.div_rpow (mul_nonneg (Tq_pos u).le (Tq_pos u').le) hξ.le, Real.rpow_neg hξ.le,
      div_eq_mul_inv]
  rw [hdiv]
  calc (2 * π)⁻¹ * ‖∫ y : ℝ, Gamma (6 + ↑u * I + (↑x + ↑y * I)) *
        Gamma (6 - ↑u' * I + (↑x + ↑y * I)) * (ξ : ℂ) ^ (-(↑x + ↑y * I)) *
        cexp ((↑x + ↑y * I) ^ 2) / (↑x + ↑y * I)‖
      ≤ (2 * π)⁻¹ * (B * J) := by gcongr
    _ = _ := by simp only [B, K, G]; ring

lemma normGG (u u' : ℝ) : ‖Gamma (6 + u * I) * Gamma (6 - u' * I)‖ =
    ‖Gamma (6 + u * I)‖ * ‖Gamma (6 + u' * I)‖ := by
  rw [norm_mul, norm_Gamma_six_sub]

/-- **Rapid decay of the lag weight**: `|W̃_{u,u'}(ξ)| ≤ C_A (T(u)T(u')/ξ)^A`. -/
theorem Wsh_decay {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u u' ξ : ℝ, 0 < ξ → ‖Wsh u u' ξ‖ ≤ C * (Tq u * Tq u' / ξ) ^ A := by
  obtain ⟨K, hK0, hK⟩ := W2sh_line_bound (x := A) (by linarith) hA.ne'
  refine ⟨K, hK0, fun u u' ξ hξ => ?_⟩
  have hW : W2sh (6 + u * I) (6 - u' * I) ξ 2 = W2sh (6 + u * I) (6 - u' * I) ξ A := by
    rcases le_total A 2 with h | h
    · exact (W2sh_shift hξ hA h (by simp; linarith) (by simp; linarith)).symm
    · exact W2sh_shift hξ (by norm_num) h (by simp; norm_num) (by simp; norm_num)
  have hGp : 0 < ‖Gamma (6 + u * I) * Gamma (6 - u' * I)‖ := norm_pos_iff.2 (Gpair_ne (u, u'))
  unfold Wsh
  rw [hW, norm_div, div_le_iff₀ hGp, normGG]
  exact hK u u' ξ hξ

/-- **The lag weight is `1 + O(ξ/(T(u)T(u')))`**: for `0 < c ≤ 9/2`. -/
theorem Wsh_sub_one {c : ℝ} (hc0 : 0 < c) (hc : c ≤ 9 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u u' ξ : ℝ, 0 < ξ →
      ‖Wsh u u' ξ - 1‖ ≤ C * (ξ / (Tq u * Tq u')) ^ c := by
  obtain ⟨K, hK0, hK⟩ := W2sh_line_bound (x := -c) (by linarith) (by linarith)
  refine ⟨K, hK0, fun u u' ξ hξ => ?_⟩
  have hres := W2sh_residue (a := 6 + u * I) (b := 6 - u' * I) hξ (by norm_num : (0:ℝ) < 2) hc0
    (by simp; linarith) (by simp; linarith)
  have hG := Gpair_ne (u, u')
  have hGp : 0 < ‖Gamma (6 + u * I) * Gamma (6 - u' * I)‖ := norm_pos_iff.2 hG
  have hV : Wsh u u' ξ - 1 =
      W2sh (6 + u * I) (6 - u' * I) ξ (-c) / (Gamma (6 + u * I) * Gamma (6 - u' * I)) := by
    unfold Wsh
    rw [eq_div_iff hG, sub_mul, div_mul_cancel₀ _ hG, one_mul]
    linear_combination hres
  rw [hV, norm_div, div_le_iff₀ hGp, normGG]
  refine (hK u u' ξ hξ).trans (le_of_eq ?_)
  have hTT : 0 < Tq u * Tq u' := mul_pos (Tq_pos u) (Tq_pos u')
  rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), inv_div]

/-- **The lag weight bound**: `|W̃_{u,u'}(ξ)| ≤ C_A (1 + ξ/(T(u)T(u')))^{−A}` for every `A ≥ 0`. -/
theorem Wsh_bound {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u u' ξ : ℝ, 0 < ξ →
      ‖Wsh u u' ξ‖ ≤ C * (1 + ξ / (Tq u * Tq u')) ^ (-A) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := Wsh_decay (A := A + 1) (by linarith)
  obtain ⟨C₂, hC₂0, hC₂⟩ := Wsh_sub_one (c := 1) one_pos (by norm_num)
  refine ⟨2 ^ (A + 1) * (C₁ + C₂ + 1), by positivity, fun u u' ξ hξ => ?_⟩
  set r : ℝ := ξ / (Tq u * Tq u')
  have hTT : 0 < Tq u * Tq u' := mul_pos (Tq_pos u) (Tq_pos u')
  have hr : 0 < r := div_pos hξ hTT
  have h1r : 0 < 1 + r := by linarith
  have hpow : (1 + r) ^ (-A) * (1 + r) ^ A = 1 := by
    rw [← Real.rpow_add h1r]; simp
  rcases le_total r 1 with hr1 | hr1
  · -- small `r`: `|W̃| ≤ 1 + C₂ r ≤ 1 + C₂`, and `(1+r)^{−A} ≥ 2^{−A}`
    have hW : ‖Wsh u u' ξ‖ ≤ 1 + C₂ := by
      have := hC₂ u u' ξ hξ
      rw [Real.rpow_one] at this
      have h' : ‖Wsh u u' ξ‖ ≤ ‖Wsh u u' ξ - 1‖ + 1 := by
        have := norm_sub_norm_le (Wsh u u' ξ) 1; rw [norm_one] at this; linarith
      nlinarith
    have hlow : (2 : ℝ) ^ (-A) ≤ (1 + r) ^ (-A) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
    have h2A : (2 : ℝ) ^ (A + 1) * (2 : ℝ) ^ (-A) = 2 := by
      rw [← Real.rpow_add (by norm_num)]; norm_num
    calc ‖Wsh u u' ξ‖ ≤ 1 + C₂ := hW
      _ ≤ 2 ^ (A + 1) * (C₁ + C₂ + 1) * 2 ^ (-A) := by
          rw [mul_comm (2 ^ (A + 1)) _, mul_assoc, h2A]; nlinarith
      _ ≤ 2 ^ (A + 1) * (C₁ + C₂ + 1) * (1 + r) ^ (-A) := by gcongr
  · -- large `r`: `|W̃| ≤ C₁ r^{−(A+1)} ≤ C₁ 2^{A+1} (1+r)^{−A}`
    have hW := hC₁ u u' ξ hξ
    have hinv : Tq u * Tq u' / ξ = r⁻¹ := by simp only [r]; rw [inv_div]
    rw [hinv] at hW
    have hle : r⁻¹ ^ (A + 1) ≤ 2 ^ (A + 1) * (1 + r) ^ (-A) := by
      have h2r : 1 + r ≤ 2 * r := by linarith
      have e1 : r⁻¹ ^ (A + 1) = (r ^ (A + 1))⁻¹ := Real.inv_rpow hr.le _
      have e2 : (1 + r) ^ (-A) = ((1 + r) ^ A)⁻¹ := Real.rpow_neg h1r.le _
      rw [e1, e2, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos h1r _),
        inv_mul_eq_div, div_le_iff₀ (Real.rpow_pos_of_pos hr _)]
      calc (1 + r) ^ A ≤ (2 * r) ^ A := Real.rpow_le_rpow h1r.le h2r hA
        _ = 2 ^ A * r ^ A := Real.mul_rpow (by norm_num) hr.le
        _ ≤ 2 ^ (A + 1) * r ^ (A + 1) := by
            rw [Real.rpow_add (by norm_num), Real.rpow_add hr, Real.rpow_one, Real.rpow_one]
            have : 0 < 2 ^ A * r ^ A := by positivity
            nlinarith
    calc ‖Wsh u u' ξ‖ ≤ C₁ * r⁻¹ ^ (A + 1) := hW
      _ ≤ C₁ * (2 ^ (A + 1) * (1 + r) ^ (-A)) := by gcongr
      _ ≤ 2 ^ (A + 1) * (C₁ + C₂ + 1) * (1 + r) ^ (-A) := by
          have : 0 ≤ (2 : ℝ) ^ (A + 1) * (1 + r) ^ (-A) := by positivity
          nlinarith

end RamanujanTau.SelbergKey2
