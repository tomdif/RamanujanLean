/-
# Landau's theorem (Pringsheim–Landau) for Dirichlet series with nonnegative coefficients

If `a : ℕ → ℂ` takes nonnegative real values (`0 ≤ a` in `ComplexOrder`) and its L-series agrees,
on a right half-plane `Re s > x` lying inside the half-plane of absolute convergence, with an
*entire* function `F`, then the L-series converges absolutely **everywhere**
(`abscissaOfAbsConv a = ⊥`).

Proof (Landau): expand `F` in its Taylor series at a real point `c > x`; this converges on all of
`ℂ` (`Complex.hasSum_taylorSeries_of_entire`). At real `σ < c` the `j`-th term is
`(c-σ)^j/j! · ∑ₙ a(n) (log n)^j n^{-c}` (`LSeries_iteratedDeriv`), a double series of nonnegative
reals, so Tonelli (`summable_prod_of_nonneg`) lets us swap the sums, and the inner sum over `j` is
`a(n) n^{-c} e^{(c-σ) log n} = a(n) n^{-σ}`.

Mathlib has `LSeries.positive_of_differentiable_of_eqOn` (positivity of `F` on `ℝ`) but not this
convergence statement.
-/
import Mathlib.NumberTheory.LSeries.Positivity

set_option autoImplicit false

namespace RamanujanTau.LandauSigns

open Complex LSeries
open scoped ComplexOrder

lemma logMul_iterate_apply (f : ℕ → ℂ) (j n : ℕ) :
    (logMul^[j] f) n = (Real.log n : ℂ) ^ j * f n := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    simp only [LSeries.logMul, ih, ← natCast_log]
    ring

/-- Real version of `term (logMul^[j] b) x n`. -/
noncomputable def rterm (b : ℕ → ℝ) (x : ℝ) (j n : ℕ) : ℝ :=
  if n = 0 then 0 else Real.log n ^ j * b n / (n : ℝ) ^ x

lemma term_logMul_iterate (b : ℕ → ℝ) (x : ℝ) (j n : ℕ) :
    term (logMul^[j] (fun n => (b n : ℂ))) (x : ℂ) n = (rterm b x j n : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [rterm]
  · rw [term_of_ne_zero hn, logMul_iterate_apply, rterm, if_neg hn]
    simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]

lemma term_eq_rterm (b : ℕ → ℝ) (x : ℝ) (n : ℕ) :
    term (fun n => (b n : ℂ)) (x : ℂ) n = (rterm b x 0 n : ℂ) := by
  simpa using term_logMul_iterate b x 0 n

lemma rterm_nonneg {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n) (x : ℝ) (j n : ℕ) : 0 ≤ rterm b x j n := by
  unfold rterm
  split_ifs
  · exact le_rfl
  · exact div_nonneg (mul_nonneg (pow_nonneg (Real.log_natCast_nonneg n) _) (hb n))
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)

lemma summable_rterm (b : ℕ → ℝ) {x : ℝ}
    (h : abscissaOfAbsConv (fun n => (b n : ℂ)) < x) (j : ℕ) : Summable (rterm b x j) := by
  have hs := LSeriesSummable_of_abscissaOfAbsConv_lt_re
    (f := logMul^[j] (fun n => (b n : ℂ))) (s := (x : ℂ)) (by simpa using h)
  unfold LSeriesSummable at hs
  rw [show term (logMul^[j] (fun n => (b n : ℂ))) (x : ℂ) = fun n => (rterm b x j n : ℂ) from
    funext (term_logMul_iterate b x j)] at hs
  exact Complex.summable_ofReal.mp hs

lemma LSeries_logMul_iterate (b : ℕ → ℝ) (x : ℝ) (j : ℕ) :
    LSeries (logMul^[j] (fun n => (b n : ℂ))) (x : ℂ) = ((∑' n, rterm b x j n : ℝ) : ℂ) := by
  unfold LSeries
  simp_rw [term_logMul_iterate]
  exact (Complex.ofReal_tsum _).symm

/-- Landau's theorem, real-coefficient form, at a real point. -/
theorem landau_real_of_real {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n) {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) {x : ℝ} (hx : abscissaOfAbsConv (fun n => (b n : ℂ)) ≤ x)
    (hEq : {s : ℂ | x < s.re}.EqOn F (LSeries fun n => (b n : ℂ))) (σ : ℝ) :
    LSeriesSummable (fun n => (b n : ℂ)) σ := by
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = max x σ + 1 := ⟨_, rfl⟩
  have hxc : x < c := hc_def ▸ (le_max_left x σ).trans_lt (lt_add_one _)
  have hσc : σ < c := hc_def ▸ (le_max_right x σ).trans_lt (lt_add_one _)
  have hac : abscissaOfAbsConv (fun n => (b n : ℂ)) < c := hx.trans_lt (by exact_mod_cast hxc)
  have hopen : IsOpen {s : ℂ | x < s.re} := continuous_re.isOpen_preimage _ isOpen_Ioi
  have hcmem : (c : ℂ) ∈ {s : ℂ | x < s.re} := by simpa using hxc
  -- Taylor series of `F` at `c`, evaluated at `σ`
  have hT := Complex.hasSum_taylorSeries_of_entire hF (c : ℂ) (σ : ℂ)
  obtain ⟨G, hG_def⟩ : ∃ G : ℕ → ℝ,
      G = fun j => (j.factorial : ℝ)⁻¹ * (c - σ) ^ j * ∑' n, rterm b c j n := ⟨_, rfl⟩
  have hterm : ∀ j : ℕ, (j.factorial : ℂ)⁻¹ • ((σ : ℂ) - c) ^ j • iteratedDeriv j F c =
      (G j : ℂ) := by
    intro j
    rw [hEq.iteratedDeriv_of_isOpen hopen j hcmem, LSeries_iteratedDeriv j (by simpa using hac),
      LSeries_logMul_iterate]
    have hpow : ((σ : ℂ) - c) ^ j * (-1) ^ j = ((c : ℂ) - σ) ^ j := by
      rw [← mul_pow]; congr 1; ring
    simp only [smul_eq_mul, hG_def]
    push_cast
    rw [← hpow]
    ring
  simp_rw [hterm] at hT
  have hGsum : HasSum G (F σ).re := by simpa using Complex.hasSum_re hT
  -- the double series
  obtain ⟨g, hg_def⟩ : ∃ g : ℕ × ℕ → ℝ,
      g = fun p => (p.1.factorial : ℝ)⁻¹ * (c - σ) ^ p.1 * rterm b c p.1 p.2 := ⟨_, rfl⟩
  have hg0 : 0 ≤ g := by
    intro p
    rw [hg_def]
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (pow_nonneg (sub_nonneg.mpr hσc.le) _)) (rterm_nonneg hb c _ _)
  have hgs : Summable g := by
    refine (summable_prod_of_nonneg hg0).mpr ⟨fun j => ?_, ?_⟩
    · rw [hg_def]; dsimp only; exact (summable_rterm b hac j).mul_left _
    refine hGsum.summable.congr fun j => ?_
    simp only [hg_def, hG_def]
    rw [tsum_mul_left]
  have hg'0 : 0 ≤ g ∘ Prod.swap := fun p => hg0 p.swap
  have hgs' : Summable (g ∘ Prod.swap) := hgs.comp_injective Prod.swap_injective
  have hinner := ((summable_prod_of_nonneg hg'0).mp hgs').2
  have hval : ∀ n : ℕ, ∑' j, (g ∘ Prod.swap) (n, j) = rterm b σ 0 n := by
    intro n
    simp only [Function.comp_apply, Prod.swap_prod_mk, hg_def]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [rterm]
    · have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      set y : ℝ := (c - σ) * Real.log n
      have hE := (NormedSpace.expSeries_div_hasSum_exp y).mul_left (b n / (n : ℝ) ^ c)
      rw [← congrFun Real.exp_eq_exp_ℝ y] at hE
      have hfun : (fun j : ℕ => (j.factorial : ℝ)⁻¹ * (c - σ) ^ j * rterm b c j n) =
          fun j : ℕ => b n / (n : ℝ) ^ c * (y ^ j / j.factorial) := by
        funext j
        simp only [rterm, if_neg hn, y, mul_pow]
        ring
      rw [hfun, hE.tsum_eq]
      simp only [rterm, if_neg hn, pow_zero, one_mul]
      rw [Real.rpow_def_of_pos hn', Real.rpow_def_of_pos hn']
      have hsplit : Real.exp (Real.log n * c) = Real.exp (Real.log n * σ) * Real.exp y := by
        rw [← Real.exp_add]; congr 1; simp only [y]; ring
      rw [hsplit]
      field_simp
  rw [show (fun n => ∑' j, (g ∘ Prod.swap) (n, j)) = rterm b σ 0 from funext hval] at hinner
  unfold LSeriesSummable
  rw [show term (fun n => (b n : ℂ)) (σ : ℂ) = fun n => (rterm b σ 0 n : ℂ) from
    funext (term_eq_rterm b σ)]
  exact Complex.summable_ofReal.mpr hinner

/-- **Landau's theorem** (real-coefficient form): if `b ≥ 0` and the L-series of `b` agrees with an
entire function on a right half-plane `Re s > x` with `x ≥ abscissaOfAbsConv b`, then the
L-series of `b` converges absolutely at every `s ∈ ℂ`. -/
theorem landau_real {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n) {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) {x : ℝ} (hx : abscissaOfAbsConv (fun n => (b n : ℂ)) ≤ x)
    (hEq : {s : ℂ | x < s.re}.EqOn F (LSeries fun n => (b n : ℂ))) (s : ℂ) :
    LSeriesSummable (fun n => (b n : ℂ)) s :=
  (landau_real_of_real hb hF hx hEq s.re).of_re_le_re (by simp)

/-- **Landau's theorem** (`ComplexOrder` form, matching `LSeries.positive_of_differentiable_of_eqOn`):
if `0 ≤ a`, and `LSeries a` agrees with an entire function `F` on `Re s > x`, where
`abscissaOfAbsConv a ≤ x`, then `LSeries a` converges absolutely at every `s`. -/
theorem landau {a : ℕ → ℂ} (ha : 0 ≤ a) {F : ℂ → ℂ} (hF : Differentiable ℂ F) {x : ℝ}
    (hx : abscissaOfAbsConv a ≤ x) (hEq : {s : ℂ | x < s.re}.EqOn F (LSeries a)) (s : ℂ) :
    LSeriesSummable a s := by
  have hab : a = fun n => ((a n).re : ℂ) := by
    funext n
    exact Complex.ext (by simp) (by simpa using ((Complex.nonneg_iff.mp (ha n)).2).symm)
  rw [hab] at hx hEq ⊢
  exact landau_real (fun n => (Complex.nonneg_iff.mp (ha n)).1) hF hx hEq s

/-- Landau's theorem, abscissa form: the abscissa of absolute convergence is `⊥`. -/
theorem landau_abscissa {a : ℕ → ℂ} (ha : 0 ≤ a) {F : ℂ → ℂ} (hF : Differentiable ℂ F) {x : ℝ}
    (hx : abscissaOfAbsConv a ≤ x) (hEq : {s : ℂ | x < s.re}.EqOn F (LSeries a)) :
    abscissaOfAbsConv a = ⊥ := by
  refine (EReal.eq_bot_iff_forall_lt _).mpr fun y => ?_
  exact ((landau ha hF hx hEq ((y - 1 : ℝ) : ℂ)).abscissaOfAbsConv_le).trans_lt
    (by simp only [ofReal_re]; exact_mod_cast sub_one_lt y)

end RamanujanTau.LandauSigns
