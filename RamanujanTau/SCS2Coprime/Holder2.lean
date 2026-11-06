/-
# Item 2 (part 2): **`norm_QAB_le`**, Hölder for `Ψ_{a,b}` on `Γ₀(ab)\(ℍ×ℍ)`

`‖∫ Ψ_{a,b} conj ft‖ ≤ ½ √(c² q⁴ · 8R) √(2 ‖Σ_{h ∈ Γ₀(q)} I(h)‖)`, `q = ab`, `c = M (ab)^{−6} R⁶`.
-/
import RamanujanTau.SCS2Coprime.Holder

set_option autoImplicit false

namespace RamanujanTau.SCS2Coprime

open MeasureTheory Set Complex CongruenceSubgroup
open UpperHalfPlane hiding I
open RamanujanTau.SCSProof RamanujanTau.SCSSharp RamanujanTau.RankinError
open RamanujanTau.EisensteinReal.Horo (Uset)
open scoped MatrixGroups ENNReal Real ComplexConjugate

lemma continuous_scl (c : ℕ+) : Continuous (scl c) :=
  continuous_induced_rng.2 (continuous_const.mul UpperHalfPlane.continuous_coe)

lemma measurable_PsiAB (a b : ℕ+) : Measurable fun p : ℍ × ℍ => PsiAB a b p.1 p.2 := by
  unfold PsiAB
  refine Continuous.measurable ?_
  refine ((Continuous.pow ?_ 12).mul (continuous_Delta.comp ((continuous_scl a).comp
    continuous_fst))).mul (Complex.continuous_conj.comp (continuous_Delta.comp
      ((continuous_scl b).comp continuous_snd)))
  exact (UpperHalfPlane.continuous_coe.comp continuous_fst).sub
    (Complex.continuous_conj.comp (UpperHalfPlane.continuous_coe.comp continuous_snd))

variable (P : Par) {a b : ℕ+} {M : ℝ}

lemma Dh_nonneg (p : ℍ × ℍ) : 0 ≤ Dh p.1 p.2 := by
  unfold Dh; exact div_nonneg (Complex.normSq_nonneg _) (mul_pos p.1.im_pos p.2.im_pos).le

lemma norm_PsiAB_le_c (hM : ∀ z w : ℍ, ‖PsiAB a b z w‖ ≤ M / ((a : ℝ) * b) ^ 6 *
      (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ 6) (hM0 : 0 ≤ M)
    (p : ℍ × ℍ) (hp : Dh p.1 p.2 ≤ Rθ P) :
    ‖PsiAB a b p.1 p.2‖ ≤ M / ((a : ℝ) * b) ^ 6 * Rθ P ^ 6 := by
  refine (hM p.1 p.2).trans ?_
  have hD0 := Dh_nonneg p
  show M / ((a : ℝ) * b) ^ 6 * Dh p.1 p.2 ^ 6 ≤ _
  gcongr

lemma norm_PsiAB_ft_le (hM : ∀ z w : ℍ, ‖PsiAB a b z w‖ ≤ M / ((a : ℝ) * b) ^ 6 *
      (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ 6) (hM0 : 0 ≤ M)
    (p : ℍ × ℍ) :
    ‖PsiAB a b p.1 p.2 * conj (ft P p)‖ ≤ M / ((a : ℝ) * b) ^ 6 * Rθ P ^ 6 * ‖ft P p‖ := by
  rw [norm_mul, Complex.norm_conj]
  by_cases h : ft P p = 0
  · simp [h]
  gcongr
  exact norm_PsiAB_le_c P hM hM0 p (Dh_le_of_ft P p h)

lemma tsum_PsiAB_ft (hM : ∀ z w : ℍ, ‖PsiAB a b z w‖ ≤ M / ((a : ℝ) * b) ^ 6 *
      (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ 6) (hM0 : 0 ≤ M)
    (p : ℍ × ℍ) :
    ∑' γ : SL(2, ℤ), PsiAB a b (dsmul γ p).1 (dsmul γ p).2 * conj (ft P (dsmul γ p)) =
      ∑' x : RCos (Gamma0 ((a * b : ℕ+) : ℕ)), PsiAB a b (dsmul x.out p).1 (dsmul x.out p).2 *
        conj (PtQ P ((a * b : ℕ+) : ℕ) (dsmul x.out p)) := by
  have hs : Summable fun γ : SL(2, ℤ) =>
      PsiAB a b (dsmul γ p).1 (dsmul γ p).2 * conj (ft P (dsmul γ p)) := by
    refine Summable.of_norm_bounded ((summable_norm_ft_dsmul P p).mul_left
      (M / ((a : ℝ) * b) ^ 6 * Rθ P ^ 6)) fun γ => ?_
    exact norm_PsiAB_ft_le P hM hM0 (dsmul γ p)
  rw [tsum_coset _ _ hs]
  refine tsum_congr fun x => ?_
  simp_rw [dsmul_mul]
  have hinv : ∀ h : Gamma0 ((a * b : ℕ+) : ℕ),
      PsiAB a b (dsmul h (dsmul x.out p)).1 (dsmul h (dsmul x.out p)).2 =
        PsiAB a b (dsmul x.out p).1 (dsmul x.out p).2 := fun h =>
    PsiAB_smul_Gamma0 a b h h.2 _ _
  simp_rw [hinv]
  rw [tsum_mul_left, ← Complex.conj_tsum]
  rfl

/-- **Hölder on `Γ₀(ab)\(ℍ×ℍ)`.** -/
theorem norm_QAB_le (hM0 : 0 ≤ M) (hM : ∀ z w : ℍ, ‖PsiAB a b z w‖ ≤ M / ((a : ℝ) * b) ^ 6 *
      (Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (z.im * w.im)) ^ 6) :
    ‖∫ p, PsiAB a b p.1 p.2 * conj (ft P p)‖ ≤
      (1 / 2) * Real.sqrt ((M / ((a : ℝ) * b) ^ 6 * Rθ P ^ 6) ^ 2 *
        (((a * b : ℕ+) : ℕ) : ℝ) ^ 4 * (8 * Rθ P)) *
        Real.sqrt (2 * ‖∑' h : Gamma0 ((a * b : ℕ+) : ℕ), Iγ P h‖) := by
  set q : ℕ := ((a * b : ℕ+) : ℕ) with hqdef
  have hq : 1 ≤ q := PNat.one_le _
  haveI := finite_RCos_Gamma0 q hq
  haveI := Fintype.ofFinite (RCos (Gamma0 q))
  set R := Rθ P
  have hR := one_le_Rθ P
  set c := M / ((a : ℝ) * b) ^ 6 * R ^ 6 with hcdef
  have hc0 : 0 ≤ c := by positivity
  set k : ℝ := (Fintype.card (RCos (Gamma0 q)) : ℝ)
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  have hk : k ≤ (q : ℝ) ^ 4 := by
    have := card_RCos_Gamma0_le q hq
    rw [Nat.card_eq_fintype_card] at this
    show ((Fintype.card (RCos (Gamma0 q)) : ℕ) : ℝ) ≤ _
    exact_mod_cast this
  -- unfolding of `Ψ conj ft`
  set g : ℍ × ℍ → ℂ := fun p => PsiAB a b p.1 p.2 * conj (ft P p) with hgdef
  have hgm : Measurable g :=
    (measurable_PsiAB a b).mul (Complex.continuous_conj.measurable.comp (measurable_ft P))
  have hgpt : ∀ p, ‖g p‖ₑ ≤ ENNReal.ofReal c * ‖ft P p‖ₑ := by
    intro p
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul hc0]
    exact ENNReal.ofReal_le_ofReal (norm_PsiAB_ft_le P hM hM0 p)
  have hgi : ∫⁻ p, ‖g p‖ₑ ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := ENNReal.ofReal c * ∫⁻ p, ‖ft P p‖ₑ)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lintegral_ft_ne_top P)) ?_
    rw [← lintegral_const_mul _ (measurable_ft P).enorm]
    exact lintegral_mono hgpt
  have h2Q := integral_unfold2 g hgm hgi
  -- measurability of the ball
  have hmD : Measurable fun q : ℍ × ℍ => Dh q.1 q.2 := by
    unfold Dh
    refine Measurable.div ?_ ((measurable_im_H.comp measurable_fst).mul
      (measurable_im_H.comp measurable_snd))
    exact Complex.continuous_normSq.measurable.comp
      ((UpperHalfPlane.measurable_coe.comp measurable_fst).sub
        (Complex.continuous_conj.measurable.comp (UpperHalfPlane.measurable_coe.comp measurable_snd)))
  have hmS : MeasurableSet {q : ℍ × ℍ | Dh q.1 q.2 ≤ R} := measurableSet_le hmD measurable_const
  set F : ℍ × ℍ → ℝ≥0∞ := fun p => indU p * ENNReal.ofReal (c * Real.sqrt k) *
    {q : ℍ × ℍ | Dh q.1 q.2 ≤ R}.indicator 1 p
  set G : ℍ × ℍ → ℝ≥0∞ := fun p => indU p * ENNReal.ofReal (Real.sqrt (SQ P q p))
  have hFm : Measurable F := (measurable_indU.mul measurable_const).mul
    (measurable_one.indicator hmS)
  have hGm : Measurable G := measurable_indU.mul
    (ENNReal.measurable_ofReal.comp (measurable_SQ P q hq).sqrt)
  -- the pointwise real bound
  have hreal : ∀ p : ℍ × ℍ, Dh p.1 p.2 ≤ R →
      ‖∑' γ : SL(2, ℤ), g (dsmul γ p)‖ ≤ c * Real.sqrt k * Real.sqrt (SQ P q p) := by
    intro p hD
    rw [tsum_PsiAB_ft P hM hM0 p, tsum_fintype]
    have hSQ : SQ P q p = ∑ x : RCos (Gamma0 q), ‖PtQ P q (dsmul x.out p)‖ ^ 2 := by
      unfold SQ; rw [tsum_fintype]
    have h1 : ‖∑ x : RCos (Gamma0 q), PsiAB a b (dsmul x.out p).1 (dsmul x.out p).2 *
        conj (PtQ P q (dsmul x.out p))‖ ≤
        c * ∑ x : RCos (Gamma0 q), ‖PtQ P q (dsmul x.out p)‖ := by
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun x _ => ?_
      rw [norm_mul, Complex.norm_conj]
      gcongr
      refine norm_PsiAB_le_c P hM hM0 _ ?_
      show Dh (x.out • p.1) (x.out • p.2) ≤ R
      rw [Dh_smul]; exact hD
    have h2 : ∑ x : RCos (Gamma0 q), ‖PtQ P q (dsmul x.out p)‖ ≤
        Real.sqrt k * Real.sqrt (SQ P q p) := by
      rw [← Real.sqrt_mul hk0, Real.le_sqrt (Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (mul_nonneg hk0 (SQ_nonneg P q p)), hSQ]
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (RCos (Gamma0 q))))
        (f := fun x => ‖PtQ P q (dsmul x.out p)‖)
      simpa [k] using this
    calc _ ≤ c * ∑ x : RCos (Gamma0 q), ‖PtQ P q (dsmul x.out p)‖ := h1
      _ ≤ c * (Real.sqrt k * Real.sqrt (SQ P q p)) := by gcongr
      _ = _ := by ring
  have hzero : ∀ p : ℍ × ℍ, ¬ Dh p.1 p.2 ≤ R → ∑' γ : SL(2, ℤ), g (dsmul γ p) = 0 := by
    intro p hD
    have : ∀ γ : SL(2, ℤ), g (dsmul γ p) = 0 := by
      intro γ
      by_cases hf : ft P (dsmul γ p) = 0
      · simp [g, hf]
      · exfalso; apply hD
        have := Dh_le_of_ft P _ hf
        simp only [dsmul] at this
        rwa [Dh_smul] at this
    simp [this]
  have hpt : ∀ p, ‖indUC p * ∑' γ : SL(2, ℤ), g (dsmul γ p)‖ₑ ≤ (F * G) p := by
    intro p
    rw [enorm_indUC_mul]
    simp only [Pi.mul_apply, F, G]
    by_cases hD : Dh p.1 p.2 ≤ R
    · rw [indicator_of_mem (show p ∈ {q : ℍ × ℍ | Dh q.1 q.2 ≤ R} from hD), Pi.one_apply,
        mul_one]
      unfold indU
      by_cases hU : p.1 ∈ Uset
      · rw [indicator_of_mem hU, Pi.one_apply, one_mul, one_mul, one_mul,
          ← ENNReal.ofReal_mul (by positivity), ← ofReal_norm_eq_enorm]
        exact ENNReal.ofReal_le_ofReal (hreal p hD)
      · rw [indicator_of_notMem hU]; simp
    · rw [hzero p hD]; simp
  -- Hölder
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
    hFm.aemeasurable hGm.aemeasurable
  have hF2 : ∫⁻ p, F p ^ (2 : ℝ) ≤ ENNReal.ofReal ((c * Real.sqrt k) ^ 2 * (8 * R)) := by
    have e : ∀ p, F p ^ (2 : ℝ) = ENNReal.ofReal ((c * Real.sqrt k) ^ 2) *
        (indU p * {q : ℍ × ℍ | Dh q.1 q.2 ≤ R}.indicator 1 p) := by
      intro p
      simp only [F]
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
        indU_sq]
      have hI : ({q : ℍ × ℍ | Dh q.1 q.2 ≤ R}.indicator (1 : ℍ × ℍ → ℝ≥0∞) p) ^ (2 : ℝ) =
          {q : ℍ × ℍ | Dh q.1 q.2 ≤ R}.indicator 1 p := by
        unfold indicator; split_ifs <;> simp
      rw [hI, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
      norm_num
      ring
    simp_rw [e]
    rw [lintegral_const_mul _ (measurable_indU.mul (measurable_one.indicator hmS))]
    calc ENNReal.ofReal ((c * Real.sqrt k) ^ 2) *
          ∫⁻ p, indU p * {q : ℍ × ℍ | Dh q.1 q.2 ≤ R}.indicator 1 p
        ≤ ENNReal.ofReal ((c * Real.sqrt k) ^ 2) * ENNReal.ofReal (8 * R) := by
          gcongr; exact lintegral_U_ball' R hR
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]
  have hG2 : ∫⁻ p, G p ^ (2 : ℝ) = ∫⁻ p, indU p * ENNReal.ofReal (SQ P q p) := by
    refine lintegral_congr fun p => ?_
    simp only [G]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), indU_sq,
      ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num), Real.rpow_two,
      Real.sq_sqrt (SQ_nonneg P q p)]
  -- finiteness of `∫ G²`
  have hGfin : ∫⁻ p, indU p * ENNReal.ofReal (SQ P q p) ≠ ∞ := by
    set g' : ℍ × ℍ → ℂ := fun p => ft P p * conj (PtQ P q p)
    have hg'm : Measurable fun p => ‖g' p‖ₑ :=
      ((measurable_ft P).mul (Complex.continuous_conj.measurable.comp
        (measurable_PtQ P q))).enorm
    have h1 := lintegral_unfold2 (fun p => ‖g' p‖ₑ) hg'm
    have hfin' : ∫⁻ p, ‖g' p‖ₑ ≠ ∞ := by
      refine ne_top_of_le_ne_top (b := (N0 P : ℝ≥0∞) * ∫⁻ p, ‖ft P p‖ₑ)
        (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (lintegral_ft_ne_top P)) ?_
      rw [← lintegral_const_mul _ (measurable_ft P).enorm]
      exact lintegral_mono fun p => enorm_ft_PtQ_le P q p
    refine ne_top_of_le_ne_top (b := 2 * ∫⁻ p, ‖g' p‖ₑ)
      (ENNReal.mul_ne_top (by simp) hfin') ?_
    rw [← h1]
    refine lintegral_mono fun p => ?_
    gcongr
    have e : ENNReal.ofReal (SQ P q p) = ‖∑' γ : SL(2, ℤ), g' (dsmul γ p)‖ₑ := by
      rw [tsum_ft_PtQ P q p, ← ofReal_norm_eq_enorm, Complex.norm_real,
        Real.norm_of_nonneg (SQ_nonneg P q p)]
    rw [e]
    exact enorm_tsum_le_tsum_enorm
  have hFfin : ∫⁻ p, F p ^ (2 : ℝ) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hF2
  -- assemble
  have hnorm : ‖(2 : ℂ) * ∫ p, g p‖ ≤
      (∫⁻ p, ‖indUC p * ∑' γ : SL(2, ℤ), g (dsmul γ p)‖ₑ).toReal := by
    rw [← h2Q]; exact norm_integral_le_toReal _
  have hle1 : (∫⁻ p, ‖indUC p * ∑' γ : SL(2, ℤ), g (dsmul γ p)‖ₑ).toReal ≤
      ((∫⁻ p, F p ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) * (∫⁻ p, G p ^ (2 : ℝ)) ^ (1 / (2 : ℝ))).toReal := by
    refine ENNReal.toReal_mono ?_ ((lintegral_mono hpt).trans hH)
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hFfin)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by rw [hG2]; exact hGfin))
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow, hG2] at hle1
  have hA : ((∫⁻ p, F p ^ (2 : ℝ)).toReal) ^ (1 / (2 : ℝ)) ≤
      Real.sqrt (c ^ 2 * (q : ℝ) ^ 4 * (8 * R)) := by
    rw [← Real.sqrt_eq_rpow]
    refine Real.sqrt_le_sqrt ?_
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hF2
    rw [ENNReal.toReal_ofReal (by positivity)] at this
    refine this.trans (le_of_eq_of_le (by rw [mul_pow, Real.sq_sqrt hk0]) ?_)
    gcongr
  have hB : ((∫⁻ p, indU p * ENNReal.ofReal (SQ P q p)).toReal) ^ (1 / (2 : ℝ)) ≤
      Real.sqrt (2 * ‖∑' h : Gamma0 q, Iγ P h‖) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt (lintegral_SQ_le P q hq)
  rw [norm_mul] at hnorm
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2] at hnorm
  have hfinal : 2 * ‖∫ p, g p‖ ≤
      Real.sqrt (c ^ 2 * (q : ℝ) ^ 4 * (8 * R)) * Real.sqrt (2 * ‖∑' h : Gamma0 q, Iγ P h‖) := by
    refine hnorm.trans (hle1.trans ?_)
    exact mul_le_mul hA hB (Real.rpow_nonneg ENNReal.toReal_nonneg _) (Real.sqrt_nonneg _)
  show ‖∫ p, g p‖ ≤ _
  linarith

end RamanujanTau.SCS2Coprime
