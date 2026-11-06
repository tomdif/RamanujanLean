/-
# R1: the windowed off-diagonal `t`-integral as a sum of single-term integrals

For fixed `x, v` and the window `φ_T` on `[T/2, 3T]`:

    ∫ φ_T(t) OffLag(t+x, v) dt = 2 Re Σ_{q=(a,b,c,d) ∈ [1,y]⁴} w(q) Σ'_{(m,n)} ∫ Fq(q; m,n; t) dt,

where `Fq = φ_T · U · (b/a)^{iu}(d/c)^{i(u+v)} · [bdn ≠ acm] sTerm` (`u = t+x`) is exactly the
integrand of `SelbergKey4.term_integral_bound`, and `w(q) = wc(a,b) wc(c,d)` (`inner_offLag_eq`).
Hence (`abs_inner_offLag_le`)

    |∫ φ_T OffLag(·+x, v)| ≤ 2 Σ_q |w(q)| ‖Σ'_p ∫ Fq(q; p)‖.

The interchange of `Σ'_p` and `∫` is dominated convergence with the bound
`|φ_T(t)| C₀ |Γ(6+iu)Γ(6−i(u+v))|^{−1}(4π²)^{−2} g(m)g(n)` (`SelbergKey2.norm_sTerm_le`).
Level 1.
-/
import RamanujanTau.SelbergKey4.Main

set_option autoImplicit false

namespace RamanujanTau.SelbergKey5

open Complex MeasureTheory Set Filter Finset RamanujanTau.HeckeAFE RamanujanTau.HeckeL
  RamanujanTau.SelbergKey RamanujanTau.SelbergKey2 RamanujanTau.SelbergKey4
open scoped Real

/-- The quadruples `[1,y]⁴`. -/
def Q4 (y : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  Finset.Icc 1 y ×ˢ Finset.Icc 1 y ×ˢ Finset.Icc 1 y ×ˢ Finset.Icc 1 y

lemma quadSum_eq (β : ℕ → ℝ) (y : ℕ) (u u' : ℝ) (G : ℕ → ℕ → ℕ → ℕ → ℂ) :
    quadSum β y u u' G = ∑ q ∈ Q4 y, (wc β q.1 q.2.1 : ℂ) * eph q.1 q.2.1 u *
      ((wc β q.2.2.1 q.2.2.2 : ℂ) * eph q.2.2.1 q.2.2.2 u') * G q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  unfold quadSum Q4
  simp only [Finset.sum_product]

/-- The weight `w(q) = wc(a,b) wc(c,d)`. -/
noncomputable def wq (β : ℕ → ℝ) (q : ℕ × ℕ × ℕ × ℕ) : ℝ :=
  wc β q.1 q.2.1 * wc β q.2.2.1 q.2.2.2

/-- The windowed single term (zero on the diagonal). -/
noncomputable def Fq (T x v : ℝ) (q : ℕ × ℕ × ℕ × ℕ) (p : ℕ × ℕ) (t : ℝ) : ℂ :=
  ((phiT T t : ℝ) : ℂ) * (Ush (t + x) (t + x + v) * (eph q.1 q.2.1 (t + x) *
    eph q.2.2.1 q.2.2.2 (t + x + v) *
      (if isDiag q.1 q.2.1 q.2.2.1 q.2.2.2 p then 0 else sTerm (t + x) (t + x + v) p)))

/-- The `t`-part of the domination. -/
noncomputable def Abd (T x v t : ℝ) : ℝ :=
  |phiT T t| * (C0 / ‖Gamma (6 + ((t + x : ℝ) : ℂ) * I) * Gamma (6 - ((t + x + v : ℝ) : ℂ) * I)‖ *
    (4 * π ^ 2) ^ (-(2:ℝ)))

lemma norm_eph (a b : ℕ) (u : ℝ) : ‖eph a b u‖ = 1 := by
  unfold eph
  rw [show (u : ℂ) * I * ((Real.log b - Real.log a : ℝ) : ℂ) =
    ((u * (Real.log b - Real.log a) : ℝ) : ℂ) * I by rw [Complex.ofReal_mul]; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma continuous_phiT (T : ℝ) : Continuous (phiT T) :=
  (contDiff_Phi 0).continuous.comp (continuous_id.div_const T)

lemma Abd_nonneg (T x v t : ℝ) : 0 ≤ Abd T x v t := by
  unfold Abd
  exact mul_nonneg (abs_nonneg _) (mul_nonneg (div_nonneg C0_nonneg (norm_nonneg _))
    (Real.rpow_nonneg (by positivity) _))

lemma continuous_Abd (T x v : ℝ) : Continuous (Abd T x v) := by
  unfold Abd
  have hG : Continuous fun t : ℝ =>
      Gamma (6 + ((t + x : ℝ) : ℂ) * I) * Gamma (6 - ((t + x + v : ℝ) : ℂ) * I) :=
    continuous_Gpair.comp (by fun_prop : Continuous fun t : ℝ => ((t + x, t + x + v) : ℝ × ℝ))
  refine (continuous_abs.comp (continuous_phiT T)).mul (Continuous.mul ?_ continuous_const)
  exact continuous_const.div hG.norm fun t => norm_ne_zero_iff.2 (Gpair_ne (t + x, t + x + v))

lemma continuous_Fq (T x v : ℝ) (q : ℕ × ℕ × ℕ × ℕ) (p : ℕ × ℕ) : Continuous (Fq T x v q p) := by
  have hmap : Continuous fun t : ℝ => ((t + x, t + x + v) : ℝ × ℝ) := by fun_prop
  have hU := continuous_Ush.comp hmap
  simp only [Function.comp_def] at hU
  have he1 : Continuous fun t : ℝ => eph q.1 q.2.1 (t + x) := by unfold eph; fun_prop
  have he2 : Continuous fun t : ℝ => eph q.2.2.1 q.2.2.2 (t + x + v) := by unfold eph; fun_prop
  have hs : Continuous fun t : ℝ =>
      (if isDiag q.1 q.2.1 q.2.2.1 q.2.2.2 p then 0 else sTerm (t + x) (t + x + v) p) := by
    split_ifs
    · exact continuous_const
    · have h := (continuous_sTerm p).comp hmap
      simp only [Function.comp_def] at h
      exact h
  have hφ : Continuous fun t : ℝ => ((phiT T t : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_phiT T)
  exact hφ.mul (hU.mul ((he1.mul he2).mul hs))

lemma norm_Fq_le (T x v : ℝ) (q : ℕ × ℕ × ℕ × ℕ) (p : ℕ × ℕ) (t : ℝ) :
    ‖Fq T x v q p t‖ ≤ Abd T x v t * (gt p.1 * gt p.2) := by
  unfold Fq Abd
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_Ush, one_mul, norm_mul,
    norm_mul, norm_eph, norm_eph, one_mul, one_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h := norm_sTerm_le (t + x) (t + x + v) p
  split_ifs
  · rw [norm_zero]
    exact mul_nonneg (mul_nonneg (div_nonneg C0_nonneg (norm_nonneg _))
      (Real.rpow_nonneg (by positivity) _)) (mul_nonneg (gt_nonneg _) (gt_nonneg _))
  · exact h

lemma summable_gg : Summable fun p : ℕ × ℕ => gt p.1 * gt p.2 :=
  Summable.mul_of_nonneg summable_gt summable_gt (fun m => gt_nonneg m) (fun m => gt_nonneg m)

/-- The pointwise sum over `(m,n)`. -/
lemma hasSum_Fq (T x v : ℝ) (q : ℕ × ℕ × ℕ × ℕ) (t : ℝ) :
    HasSum (fun p => Fq T x v q p t)
      (((phiT T t : ℝ) : ℂ) * (Ush (t + x) (t + x + v) * (eph q.1 q.2.1 (t + x) *
        eph q.2.2.1 q.2.2.2 (t + x + v) * (Sl (t + x) (t + x + v) -
          diagS q.1 q.2.1 q.2.2.1 q.2.2.2 (t + x) (t + x + v))))) := by
  set u := t + x
  set u' := t + x + v
  have hs : Summable fun p : ℕ × ℕ =>
      (if isDiag q.1 q.2.1 q.2.2.1 q.2.2.2 p then 0 else sTerm u u' p) :=
    Summable.of_norm_bounded (g := fun p => ‖sTerm u u' p‖) (summable_sTerm u u').norm
      fun p => by split_ifs <;> simp
  rw [Sl_sub_diagS]
  have h := hs.hasSum.mul_left (((phiT T t : ℝ) : ℂ) * (Ush u u' * (eph q.1 q.2.1 u *
    eph q.2.2.1 q.2.2.2 u')))
  convert h using 1
  · funext p; unfold Fq; simp only [u, u']; ring
  · ring

/-- `φ · OffLag` as a finite sum of the pointwise limits. -/
lemma phi_offLag_eq (β : ℕ → ℝ) (y : ℕ) (T x v t : ℝ) :
    phiT T t * OffLag β y (t + x) v =
      2 * (∑ q ∈ Q4 y, (wq β q : ℂ) * (((phiT T t : ℝ) : ℂ) * (Ush (t + x) (t + x + v) *
        (eph q.1 q.2.1 (t + x) * eph q.2.2.1 q.2.2.2 (t + x + v) * (Sl (t + x) (t + x + v) -
          diagS q.1 q.2.1 q.2.2.1 q.2.2.2 (t + x) (t + x + v)))))).re := by
  rw [lag_split, quadSum_eq]
  have e : ((phiT T t : ℝ) : ℂ) * (Ush (t + x) (t + x + v) *
      ∑ q ∈ Q4 y, (wc β q.1 q.2.1 : ℂ) * eph q.1 q.2.1 (t + x) *
        ((wc β q.2.2.1 q.2.2.2 : ℂ) * eph q.2.2.1 q.2.2.2 (t + x + v)) *
          (Sl (t + x) (t + x + v) - diagS q.1 q.2.1 q.2.2.1 q.2.2.2 (t + x) (t + x + v))) =
      ∑ q ∈ Q4 y, (wq β q : ℂ) * (((phiT T t : ℝ) : ℂ) * (Ush (t + x) (t + x + v) *
        (eph q.1 q.2.1 (t + x) * eph q.2.2.1 q.2.2.2 (t + x + v) * (Sl (t + x) (t + x + v) -
          diagS q.1 q.2.1 q.2.2.1 q.2.2.2 (t + x) (t + x + v))))) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    unfold wq; push_cast; ring
  rw [← e, Complex.re_ofReal_mul]
  ring

/-- The real terms `f_p(t) = 2 Re Σ_q w(q) Fq(q; p; t)`. -/
noncomputable def fR (β : ℕ → ℝ) (y : ℕ) (T x v : ℝ) (p : ℕ × ℕ) (t : ℝ) : ℝ :=
  2 * (∑ q ∈ Q4 y, (wq β q : ℂ) * Fq T x v q p t).re

lemma continuous_fR (β : ℕ → ℝ) (y : ℕ) (T x v : ℝ) (p : ℕ × ℕ) : Continuous (fR β y T x v p) := by
  unfold fR
  exact continuous_const.mul (Complex.continuous_re.comp (continuous_finsetSum _ fun q _ =>
    continuous_const.mul (continuous_Fq T x v q p)))

noncomputable def Wsum (β : ℕ → ℝ) (y : ℕ) : ℝ := ∑ q ∈ Q4 y, |wq β q|

lemma abs_fR_le (β : ℕ → ℝ) (y : ℕ) (T x v : ℝ) (p : ℕ × ℕ) (t : ℝ) :
    |fR β y T x v p t| ≤ (2 * Wsum β y * Abd T x v t) * (gt p.1 * gt p.2) := by
  unfold fR Wsum
  rw [abs_mul, abs_two]
  have h1 := Complex.abs_re_le_norm (∑ q ∈ Q4 y, (wq β q : ℂ) * Fq T x v q p t)
  have h2 : ‖∑ q ∈ Q4 y, (wq β q : ℂ) * Fq T x v q p t‖ ≤
      ∑ q ∈ Q4 y, |wq β q| * (Abd T x v t * (gt p.1 * gt p.2)) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_Fq_le T x v q p t) (abs_nonneg _)
  rw [← Finset.sum_mul] at h2
  nlinarith [h1, h2]

/-- **Dominated convergence: `∫ φ_T OffLag(·+x, v) = Σ'_p ∫ f_p`.** -/
theorem hasSum_integral_fR (β : ℕ → ℝ) (y : ℕ) (T x v : ℝ) :
    HasSum (fun p => ∫ t in (T / 2)..(3 * T), fR β y T x v p t)
      (∫ t in (T / 2)..(3 * T), phiT T t * OffLag β y (t + x) v) := by
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun p t => (2 * Wsum β y * Abd T x v t) * (gt p.1 * gt p.2))
    (fun p => (continuous_fR β y T x v p).aestronglyMeasurable)
    (fun p => Eventually.of_forall fun t _ => by
      rw [Real.norm_eq_abs]; exact abs_fR_le β y T x v p t)
    (Eventually.of_forall fun t _ => summable_gg.mul_left _) ?_ ?_
  · have e : (fun t => ∑' p : ℕ × ℕ, (2 * Wsum β y * Abd T x v t) * (gt p.1 * gt p.2)) =
        fun t => (2 * Wsum β y * Abd T x v t) * ∑' p : ℕ × ℕ, gt p.1 * gt p.2 := by
      funext t; exact tsum_mul_left
    rw [e]
    exact ((continuous_const.mul (continuous_Abd T x v)).mul continuous_const).intervalIntegrable _ _
  · refine Eventually.of_forall fun t _ => ?_
    rw [phi_offLag_eq]
    have hc := hasSum_sum (s := Q4 y) fun q _ => (hasSum_Fq T x v q t).mul_left (wq β q : ℂ)
    have hr := (Complex.reCLM.hasSum hc).mul_left 2
    simpa [fR] using hr

lemma integral_fR (β : ℕ → ℝ) (y : ℕ) (T x v : ℝ) (p : ℕ × ℕ) :
    ∫ t in (T / 2)..(3 * T), fR β y T x v p t =
      2 * (∑ q ∈ Q4 y, (wq β q : ℂ) * ∫ t in (T / 2)..(3 * T), Fq T x v q p t).re := by
  unfold fR
  rw [intervalIntegral.integral_const_mul]
  congr 1
  have hint : IntervalIntegrable (fun t => ∑ q ∈ Q4 y, (wq β q : ℂ) * Fq T x v q p t) volume
      (T / 2) (3 * T) :=
    (continuous_finsetSum _ fun q _ =>
      continuous_const.mul (continuous_Fq T x v q p)).intervalIntegrable _ _
  have h := Complex.reCLM.intervalIntegral_comp_comm hint
  simp only [Complex.reCLM_apply] at h
  have hs : (∫ t in (T / 2)..(3 * T), ∑ q ∈ Q4 y, (wq β q : ℂ) * Fq T x v q p t) =
      ∑ q ∈ Q4 y, ∫ t in (T / 2)..(3 * T), (wq β q : ℂ) * Fq T x v q p t :=
    intervalIntegral.integral_finsetSum (f := fun q t => (wq β q : ℂ) * Fq T x v q p t)
      fun q _ => (continuous_const.mul (continuous_Fq T x v q p)).intervalIntegrable _ _
  rw [h, hs]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  exact intervalIntegral.integral_const_mul _ _

lemma norm_integral_Fq_le (T x v : ℝ) (hT : 0 ≤ T) (q : ℕ × ℕ × ℕ × ℕ) (p : ℕ × ℕ) :
    ‖∫ t in (T / 2)..(3 * T), Fq T x v q p t‖ ≤
      (∫ t in (T / 2)..(3 * T), Abd T x v t) * (gt p.1 * gt p.2) := by
  rw [← intervalIntegral.integral_mul_const]
  refine intervalIntegral.norm_integral_le_of_norm_le (by linarith)
    (Eventually.of_forall fun t _ => norm_Fq_le T x v q p t) ?_
  exact ((continuous_Abd T x v).mul continuous_const).intervalIntegrable _ _

lemma summable_integral_Fq (T x v : ℝ) (hT : 0 ≤ T) (q : ℕ × ℕ × ℕ × ℕ) :
    Summable fun p => ∫ t in (T / 2)..(3 * T), Fq T x v q p t :=
  Summable.of_norm_bounded (g := fun p => (∫ t in (T / 2)..(3 * T), Abd T x v t) *
    (gt p.1 * gt p.2)) (summable_gg.mul_left _) fun p => norm_integral_Fq_le T x v hT q p

/-- **R1: the windowed off-diagonal integral as a sum of single-term integrals.** -/
theorem inner_offLag_eq (β : ℕ → ℝ) (y : ℕ) {T : ℝ} (hT : 0 ≤ T) (x v : ℝ) :
    ∫ t in (T / 2)..(3 * T), phiT T t * OffLag β y (t + x) v =
      2 * (∑ q ∈ Q4 y, (wq β q : ℂ) *
        ∑' p : ℕ × ℕ, ∫ t in (T / 2)..(3 * T), Fq T x v q p t).re := by
  rw [← (hasSum_integral_fR β y T x v).tsum_eq]
  simp_rw [integral_fR]
  have hs : ∀ q ∈ Q4 y, Summable fun p => (wq β q : ℂ) * ∫ t in (T / 2)..(3 * T), Fq T x v q p t :=
    fun q _ => (summable_integral_Fq T x v hT q).mul_left _
  have hsum : Summable fun p : ℕ × ℕ =>
      ∑ q ∈ Q4 y, (wq β q : ℂ) * ∫ t in (T / 2)..(3 * T), Fq T x v q p t :=
    summable_sum hs
  have hre := Complex.reCLM.map_tsum hsum
  simp only [Complex.reCLM_apply] at hre
  rw [tsum_mul_left (a := (2:ℝ)), ← hre, Summable.tsum_finsetSum hs]
  simp only [tsum_mul_left]

/-- **R1, norm form.** -/
theorem abs_inner_offLag_le (β : ℕ → ℝ) (y : ℕ) {T : ℝ} (hT : 0 ≤ T) (x v : ℝ) :
    |∫ t in (T / 2)..(3 * T), phiT T t * OffLag β y (t + x) v| ≤
      2 * ∑ q ∈ Q4 y, |wq β q| * ‖∑' p : ℕ × ℕ, ∫ t in (T / 2)..(3 * T), Fq T x v q p t‖ := by
  rw [inner_offLag_eq β y hT x v, abs_mul, abs_two]
  refine mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans ?_) (by norm_num)
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun q _ => ?_))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]

end RamanujanTau.SelbergKey5
