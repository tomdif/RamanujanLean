/-
# The `u`-average of `∫_{16}^u Σ_q bG2 g g c t q dt` for a `GoodSeq`

`gavg_eq`: `(1/H)∫_X^{X+H} ∫_{16}^u Σ_q bG2 g g c t q dt du = Σ_q zzF g X H q`, where
`zzF g X H q = coefG g q · Ptil(Λ_q − c, λ_q, X, H)` (diagonal included).
-/
import RamanujanTau.TwistedMoment.TwAFE
import RamanujanTau.GoodSecondTerm2.Avg

set_option autoImplicit false

namespace RamanujanTau.TwistedMoment

variable {lam : ℕ → ℝ} [GoodSeq lam]

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.ZetaAFE RamanujanTau.GoodSecondTerm RamanujanTau.GoodSecondTerm2
open scoped Interval

variable (lam) in
/-- The full averaged pair term (diagonal included). -/
noncomputable def zzF (T H : ℝ) (q : ℕ × ℕ) : ℂ :=
  (coefG lam q : ℂ) * Ptil (lg q.1 + lg q.2 - GoodSeq.c lam) (lg q.2 - lg q.1) T H

lemma zzF_off (T H : ℝ) {q : ℕ × ℕ} (hq : q.1 ≠ q.2) : zzF lam T H q = zz lam T H q := by
  unfold zzF zz; rw [if_neg hq]

lemma bG2_eq (t : ℝ) (q : ℕ × ℕ) : bG2 lam lam (GoodSeq.c lam) t q =
    (coefG lam q : ℂ) * (cexp (t * I * ((lg q.2 - lg q.1 : ℝ) : ℂ)) *
      (WV (lg q.1 + lg q.2 - GoodSeq.c lam) t : ℂ)) := by
  unfold bG2 wq coefG WV; push_cast; ring

variable (lam) in
/-- Summable majorant. -/
noncomputable def vq (T' : ℝ) (q : ℕ × ℕ) : ℝ :=
  C1 * (c2V * Real.exp (4 * ellT T' + 2 * GoodSeq.c lam)) * (((q.1 : ℝ) + 1) ^ (-(2 : ℝ)) * ((q.2 : ℝ) + 1) ^ (-(2 : ℝ)))

lemma vq_nonneg (T' : ℝ) (q : ℕ × ℕ) : 0 ≤ vq lam T' q := by
  unfold vq; have := C1_pos; have := c2V_pos; positivity

lemma summable_vq (T' : ℝ) : Summable (vq lam T') := by
  unfold vq
  refine Summable.mul_left _ ?_
  exact Summable.mul_of_nonneg (summable_shift_rpow (s := 2) (by norm_num))
    (summable_shift_rpow (s := 2) (by norm_num)) (fun n => by positivity) (fun n => by positivity)

lemma norm_bG2_le {t T' : ℝ} (ht : 16 ≤ t) (htT : t ≤ T') (q : ℕ × ℕ) :
    ‖bG2 lam lam (GoodSeq.c lam) t q‖ ≤ vq lam T' q := by
  set c := GoodSeq.c lam
  have hl := lam_mul_exp_le (lam := lam) C1_pos.le GoodSeq.rankin (q.1 + 1) (q.2 + 1) (by omega) (by omega)
  have e1 : Real.log ((q.1 + 1 : ℕ) : ℝ) = lg q.1 := by unfold lg; push_cast; rfl
  have e2 : Real.log ((q.2 + 1 : ℕ) : ℝ) = lg q.2 := by unfold lg; push_cast; rfl
  rw [e1, e2] at hl
  unfold bG2 wq
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Complex.norm_exp]
  have he : (t * I * ((lg q.2 - lg q.1 : ℝ) : ℂ)).re = 0 := by
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im]
    ring
  rw [he, Real.exp_zero, mul_one]
  have hV0 := V_nonneg (lg q.1 + lg q.2 - c - 2 * ellT t)
  rw [abs_of_nonneg hV0]
  have hV : V (lg q.1 + lg q.2 - c - 2 * ellT t) ≤
      c2V * Real.exp (4 * ellT T' + 2 * c) * (((q.1 : ℝ) + 1) ^ (-(2 : ℝ)) * ((q.2 : ℝ) + 1) ^ (-(2 : ℝ))) := by
    refine (antitone_V (show lg q.1 + lg q.2 - c - 2 * ellT T' ≤ lg q.1 + lg q.2 - c - 2 * ellT t by
      linarith [ellT_mono (by linarith : (0 : ℝ) < t) htT])).trans ?_
    refine (V_le_exp_k (k := 2) (by norm_num) _).trans (le_of_eq ?_)
    unfold c2V lg
    rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (by positivity), ← Real.exp_add,
      mul_assoc, ← Real.exp_add]
    congr 2; ring
  unfold vq
  calc |lam (q.1 + 1) * lam (q.2 + 1)| * (Real.exp (-((lg q.1 + lg q.2) / 2)) *
        V (lg q.1 + lg q.2 - c - 2 * ellT t))
      = (|lam (q.1 + 1) * lam (q.2 + 1)| * Real.exp (-((lg q.1 + lg q.2) / 2))) *
        V (lg q.1 + lg q.2 - c - 2 * ellT t) := by ring
    _ ≤ C1 * (c2V * Real.exp (4 * ellT T' + 2 * c) *
        (((q.1 : ℝ) + 1) ^ (-(2 : ℝ)) * ((q.2 : ℝ) + 1) ^ (-(2 : ℝ)))) :=
        mul_le_mul hl hV hV0 C1_pos.le
    _ = _ := by ring

lemma continuousOn_bG2 (q : ℕ × ℕ) : ContinuousOn (fun t => bG2 lam lam (GoodSeq.c lam) t q) (Ioi 0) := by
  intro t ht
  refine ContinuousAt.continuousWithinAt ?_
  unfold bG2 wq
  have hE : ContinuousAt ellT t := (hasDerivAt_ellT ht).continuousAt
  refine ContinuousAt.mul continuousAt_const (ContinuousAt.mul (ContinuousAt.mul continuousAt_const (by fun_prop)) ?_)
  exact Complex.continuous_ofReal.continuousAt.comp (continuous_V.continuousAt.comp
    (continuousAt_const.sub (continuousAt_const.mul hE)))

/-- Per pair: the `u`-average is `zzF`. -/
lemma avg_pairF {X H : ℝ} (hX : 16 ≤ X) (hH : 0 < H) (q : ℕ × ℕ) :
    (1 / (H : ℂ)) * ∫ u in X..X + H, (∫ t in (16 : ℝ)..u, bG2 lam lam (GoodSeq.c lam) t q) = zzF lam X H q := by
  rw [avg_identity (continuousOn_bG2 q) hX hH]
  unfold zzF Ptil
  simp_rw [bG2_eq]
  rw [intervalIntegral.integral_const_mul]
  set Λ := lg q.1 + lg q.2 - GoodSeq.c lam
  have e : (∫ t in X..X + H, ((X + H - t : ℝ) : ℂ) * ((coefG lam q : ℂ) *
      (cexp (t * I * ((lg q.2 - lg q.1 : ℝ) : ℂ)) * (WV Λ t : ℂ)))) =
      (coefG lam q : ℂ) * ∫ t in X..X + H, cexp (t * I * ((lg q.2 - lg q.1 : ℝ) : ℂ)) *
        (((X + H - t) * WV Λ t : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext t; push_cast; ring
  rw [e]
  have hH0 : (H : ℂ) ≠ 0 := by exact_mod_cast hH.ne'
  set A := ∫ t in (16 : ℝ)..X, cexp (t * I * ((lg q.2 - lg q.1 : ℝ) : ℂ)) * (WV Λ t : ℂ)
  set B := ∫ t in X..X + H, cexp (t * I * ((lg q.2 - lg q.1 : ℝ) : ℂ)) * (((X + H - t) * WV Λ t : ℝ) : ℂ)
  rw [mul_add, ← mul_assoc, ← mul_assoc, one_div, inv_mul_cancel₀ hH0, one_mul]
  push_cast
  ring

/-- **The averaged identity for a `GoodSeq`.** -/
theorem gavg_eq {X H : ℝ} (hX : 16 ≤ X) (hH : 0 < H) :
    Summable (zzF lam X H) ∧
    (1 / (H : ℂ)) * ∫ u in X..X + H, (∫ t in (16 : ℝ)..u, ∑' q, bG2 lam lam (GoodSeq.c lam) t q) =
      ∑' q, zzF lam X H q := by
  set c := GoodSeq.c lam
  set T' := X + H with hT'
  have hXT : X ≤ T' := by linarith
  have h16 : (0 : ℝ) < 16 := by norm_num
  have hcI : ∀ q a b, 16 ≤ a → ContinuousOn (fun t => bG2 lam lam c t q) (Icc a b) := fun q a b ha =>
    (continuousOn_bG2 q).mono (fun x hx => lt_of_lt_of_le (by linarith) hx.1)
  -- inner swap
  have hin : ∀ u ∈ Icc X T', (∫ t in (16 : ℝ)..u, ∑' q, bG2 lam lam c t q) =
      ∑' q, ∫ t in (16 : ℝ)..u, bG2 lam lam c t q := by
    intro u hu
    exact integral_tsum_Icc (by linarith [hu.1]) (fun q => hcI q 16 u le_rfl) (summable_vq (lam := lam) T')
      (fun q t ht => norm_bG2_le ht.1 (ht.2.trans hu.2) q)
  have hII : ∀ q (u : ℝ), 16 ≤ u → IntervalIntegrable (fun t => bG2 lam lam c t q) volume 16 u := fun q u hu =>
    (hcI q 16 u le_rfl).intervalIntegrable_of_Icc hu
  have hbound : ∀ q u, u ∈ Icc X T' → ‖∫ t in (16 : ℝ)..u, bG2 lam lam c t q‖ ≤ T' * vq lam T' q := by
    intro q u hu
    have h16u : 16 ≤ u := by linarith [hu.1]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := vq lam T' q) fun t ht => ?_).trans ?_
    · rw [uIoc_of_le h16u] at ht
      exact norm_bG2_le ht.1.le (ht.2.trans hu.2) q
    · rw [abs_of_nonneg (by linarith)]
      have := vq_nonneg (lam := lam) T' q
      nlinarith [hu.2]
  have hcont : ∀ q, ContinuousOn (fun u => ∫ t in (16 : ℝ)..u, bG2 lam lam c t q) (Icc X T') := by
    intro q u hu
    have hu0 : 0 < u := by linarith [hu.1]
    exact (intervalIntegral.integral_hasDerivAt_right (hII q u (by linarith [hu.1]))
      ((continuousOn_bG2 q).stronglyMeasurableAtFilter isOpen_Ioi u hu0)
      ((continuousOn_bG2 q).continuousAt (isOpen_Ioi.mem_nhds hu0))).continuousAt.continuousWithinAt
  have hout := integral_tsum_Icc hXT hcont ((summable_vq (lam := lam) T').mul_left T') hbound
  have hcongr : (∫ u in X..X + H, (∫ t in (16 : ℝ)..u, ∑' q, bG2 lam lam c t q)) =
      ∫ u in X..X + H, ∑' q, ∫ t in (16 : ℝ)..u, bG2 lam lam c t q := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le hXT] at hu
    exact hin u hu
  -- per-pair bound for summability
  have hzb : ∀ q, ‖zzF lam X H q‖ ≤ T' * vq lam T' q := by
    intro q
    rw [← avg_pairF hX hH q, norm_mul]
    have h1 : ‖∫ u in X..X + H, (∫ t in (16 : ℝ)..u, bG2 lam lam c t q)‖ ≤ (T' * vq lam T' q) * |X + H - X| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => by
        rw [uIoc_of_le hXT] at hu
        exact hbound q u ⟨hu.1.le, hu.2⟩
    rw [show X + H - X = H by ring, abs_of_pos hH] at h1
    have hn : ‖(1 / (H : ℂ))‖ = 1 / H := by
      rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
    rw [hn]
    calc 1 / H * ‖∫ u in X..X + H, (∫ t in (16 : ℝ)..u, bG2 lam lam c t q)‖ ≤ 1 / H * ((T' * vq lam T' q) * H) := by
          gcongr
      _ = T' * vq lam T' q := by field_simp
  refine ⟨Summable.of_norm_bounded ((summable_vq (lam := lam) T').mul_left T') hzb, ?_⟩
  rw [hcongr, hout, ← tsum_mul_left]
  exact tsum_congr fun q => avg_pairF hX hH q

end RamanujanTau.TwistedMoment
