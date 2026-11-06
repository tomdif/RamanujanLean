/-
# The SCS region: pairs `n = m + h`, `m ≥ M₀`, `1 ≤ h < h₂`

`zz_eq_rr`: `zz(m, m+h) = λ(M)λ(M+h) [∫_{16}^T r_t(M) dt + (1/H)∫_T^{T+H} (T+H−t) r_t(M) dt]`.
`norm_Spart_h`: `‖Σ_{k≥0} zz(M₀+k, M₀+k+h)‖ ≤ (T+H) K h^{1/21} (M₀^{−1/42} + (T+H) h M₀^{−1−1/42})`.
-/
import RamanujanTau.TwistedMoment.Regions
import RamanujanTau.ZetaAFE.Ingham

set_option autoImplicit false

namespace RamanujanTau.TwistedMoment

variable {lam : ℕ → ℝ} [GoodSeq lam]

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.ZetaAFE RamanujanTau.GoodSecondTerm RamanujanTau.GoodSecondTerm2
open scoped Interval

lemma rr_eq (t : ℝ) (m n : ℕ) :
    rr lam t ((n : ℝ) - m) ((m : ℝ) + 1) = ((Real.exp (-((lg m + lg n) / 2)) : ℝ) : ℂ) *
      (cexp (t * I * ((lg n - lg m : ℝ) : ℂ)) * (WV (lg m + lg n - GoodSeq.c lam) t : ℂ)) := by
  unfold rr WV lg
  rw [show (m : ℝ) + 1 + ((n : ℝ) - m) = (n : ℝ) + 1 by ring]
  rw [show Real.log ((m : ℝ) + 1) + Real.log ((n : ℝ) + 1) - (GoodSeq.c lam + 2 * ellT t) =
    Real.log ((m : ℝ) + 1) + Real.log ((n : ℝ) + 1) - GoodSeq.c lam - 2 * ellT t by ring]
  ring

lemma zz_eq_rr (T H : ℝ) {m n : ℕ} (hmn : m < n) :
    zz lam T H (m, n) = ((lam (m + 1) * lam (n + 1) : ℝ) : ℂ) *
      ((∫ t in (16 : ℝ)..T, rr lam t ((n : ℝ) - m) ((m : ℝ) + 1)) +
        (1 / (H : ℂ)) * ∫ t in T..T + H, ((T + H - t : ℝ) : ℂ) * rr lam t ((n : ℝ) - m) ((m : ℝ) + 1)) := by
  unfold zz
  rw [if_neg hmn.ne]
  unfold coefG
  simp only
  unfold Ptil
  simp_rw [rr_eq]
  rw [intervalIntegral.integral_const_mul]
  have e2 : (∫ t in T..T + H, ((T + H - t : ℝ) : ℂ) * (((Real.exp (-((lg m + lg n) / 2)) : ℝ) : ℂ) *
      (cexp (t * I * ((lg n - lg m : ℝ) : ℂ)) * (WV (lg m + lg n - GoodSeq.c lam) t : ℂ)))) =
      ((Real.exp (-((lg m + lg n) / 2)) : ℝ) : ℂ) *
        ∫ t in T..T + H, cexp (t * I * ((lg n - lg m : ℝ) : ℂ)) * (((T + H - t) * WV (lg m + lg n - GoodSeq.c lam) t : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext t; push_cast; ring
  rw [e2]
  push_cast
  ring

lemma lam_sq_le {A : ℝ} (hA : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, lam n ^ 2 ≤ A * N) (n : ℕ) :
    lam n ^ 2 ≤ A * n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [lam_zero]
  · refine le_trans ?_ (hA n)
    exact Finset.single_le_sum (f := fun k => lam k ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_Icc.mpr ⟨h, le_rfl⟩)

lemma abs_lam_mul_le {A : ℝ} (hA0 : 0 ≤ A) (hA : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, lam n ^ 2 ≤ A * N) (a b : ℕ) :
    |lam a * lam b| ≤ A * Real.sqrt ((a : ℝ) * b) := by
  have ha := lam_sq_le hA a
  have hb := lam_sq_le hA b
  rw [abs_mul]
  have h1 : |lam a| ≤ Real.sqrt (A * a) := Real.abs_le_sqrt ha
  have h2 : |lam b| ≤ Real.sqrt (A * b) := Real.abs_le_sqrt hb
  calc |lam a| * |lam b| ≤ Real.sqrt (A * a) * Real.sqrt (A * b) :=
        mul_le_mul h1 h2 (abs_nonneg _) (Real.sqrt_nonneg _)
    _ = A * Real.sqrt ((a : ℝ) * b) := by
        rw [← Real.sqrt_mul (by positivity), show A * a * (A * b) = A ^ 2 * (a * b) by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq hA0]

end RamanujanTau.TwistedMoment

namespace RamanujanTau.TwistedMoment

variable {lam : ℕ → ℝ} [GoodSeq lam]

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.ZetaAFE RamanujanTau.GoodSecondTerm RamanujanTau.GoodSecondTerm2
open scoped Interval

lemma lam_mul_exp_le {A : ℝ} (hA0 : 0 ≤ A) (hA : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, lam n ^ 2 ≤ A * N)
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    |lam a * lam b| * Real.exp (-((Real.log a + Real.log b) / 2)) ≤ A := by
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have hs : Real.exp (-((Real.log a + Real.log b) / 2)) * Real.sqrt ((a : ℝ) * b) = 1 := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity), Real.log_mul har.ne' hbr.ne',
      ← Real.exp_add]; simp; ring_nf
  have := abs_lam_mul_le hA0 hA a b
  have he := Real.exp_pos (-((Real.log a + Real.log b) / 2))
  calc |lam a * lam b| * Real.exp (-((Real.log a + Real.log b) / 2))
      ≤ A * Real.sqrt ((a : ℝ) * b) * Real.exp (-((Real.log a + Real.log b) / 2)) := by gcongr
    _ = A := by rw [mul_assoc, mul_comm (Real.sqrt _), hs, mul_one]

lemma continuousOn_rr (h x : ℝ) {a b : ℝ} (ha : 0 < a) : ContinuousOn (fun t => rr lam t h x) (Icc a b) := by
  unfold rr
  refine ContinuousOn.mul (ContinuousOn.mul continuousOn_const (by fun_prop)) ?_
  refine Complex.continuous_ofReal.comp_continuousOn ?_
  exact continuous_V.comp_continuousOn (continuousOn_const.sub (continuousOn_const.add (continuousOn_const.mul (continuousOn_ellT ha))))

noncomputable def c2V : ℝ := Real.exp (2 ^ 2) / (2 * Real.sqrt Real.pi)

lemma c2V_pos : 0 < c2V := by unfold c2V; have := Real.sqrt_pos.mpr Real.pi_pos; positivity

/-- Uniform bound `‖λλ r_t(M)‖ ≤ A c E⁴ M^{−4}` for `t ≤ T'`. -/
lemma norm_F_le {A : ℝ} (hA0 : 0 ≤ A) (hA : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, lam n ^ 2 ≤ A * N)
    (h : ℕ) (M : ℕ) (hM : 1 ≤ M) {t T' : ℝ} (ht : 0 < t) (htT : t ≤ T') :
    ‖((lam M * lam (M + h) : ℝ) : ℂ) * rr lam t h M‖ ≤
      A * (c2V * Real.exp (4 * ellT T' + 2 * GoodSeq.c lam)) * ((M : ℝ) ^ (-(4 : ℝ))) := by
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  unfold rr
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Complex.norm_exp]
  have he : (t * I * ((Real.log ((M : ℝ) + h) - Real.log M : ℝ) : ℂ)).re = 0 := by
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im]
    ring
  rw [he, Real.exp_zero, mul_one]
  have hl := lam_mul_exp_le hA0 hA M (M + h) hM (by omega)
  push_cast at hl
  have hV0 := V_nonneg (Real.log M + Real.log ((M : ℝ) + h) - (GoodSeq.c lam + 2 * ellT t))
  rw [abs_of_nonneg hV0]
  have hlogN : Real.log M ≤ Real.log ((M : ℝ) + h) := Real.log_le_log hM0 (by linarith [Nat.cast_nonneg (α := ℝ) h])
  have hV : V (Real.log M + Real.log ((M : ℝ) + h) - (GoodSeq.c lam + 2 * ellT t)) ≤ c2V * Real.exp (4 * ellT T' + 2 * GoodSeq.c lam) * (M : ℝ) ^ (-(4 : ℝ)) := by
    refine (antitone_V (show 2 * Real.log M - 2 * ellT T' - GoodSeq.c lam ≤ Real.log M + Real.log ((M : ℝ) + h) - (GoodSeq.c lam + 2 * ellT t) by
      linarith [ellT_mono ht htT])).trans ?_
    refine (V_le_exp_k (k := 2) (by norm_num) _).trans (le_of_eq ?_)
    unfold c2V
    rw [Real.rpow_def_of_pos hM0, mul_assoc, ← Real.exp_add]; congr 2; ring
  calc |lam M * lam (M + h)| * (Real.exp (-((Real.log M + Real.log ((M : ℝ) + h)) / 2)) *
        V (Real.log M + Real.log ((M : ℝ) + h) - (GoodSeq.c lam + 2 * ellT t)))
      ≤ A * (c2V * Real.exp (4 * ellT T' + 2 * GoodSeq.c lam) * (M : ℝ) ^ (-(4 : ℝ))) := by
        rw [← mul_assoc]; exact mul_le_mul hl hV hV0 hA0
    _ = A * (c2V * Real.exp (4 * ellT T' + 2 * GoodSeq.c lam)) * ((M : ℝ) ^ (-(4 : ℝ))) := by ring

lemma summable_M4 (a : ℕ) : Summable fun k : ℕ => (((a + 1 + k : ℕ) : ℝ) ^ (-(4 : ℝ))) := by
  have := (summable_nat_add_iff (a + 1)).mpr (summable_rpow_nat (p := 4) (by norm_num))
  refine this.congr fun k => ?_
  congr 1; push_cast; ring

/-- **The SCS region, one shift `h`.** -/
theorem norm_Spart_h : ∃ K : ℝ, 0 ≤ K ∧ ∀ (lam : ℕ → ℝ) [GoodSeq lam] (T H : ℝ) (a h : ℕ), 16 ≤ T → 0 < H → 1 ≤ h → h ≤ a →
    Summable (fun k : ℕ => zz lam T H (a + k, a + k + h)) ∧
    ‖∑' k : ℕ, zz lam T H (a + k, a + k + h)‖ ≤
      (T + H) * (K * (h : ℝ) ^ (1 / 21 : ℝ) * ((a : ℝ) ^ (-(1 / 42 : ℝ)) +
        (T + H) * h * (a : ℝ) ^ (-(1 + 1 / 42 : ℝ)))) := by
  obtain ⟨K, hK0, hK⟩ := scs_tsum
  refine ⟨K, hK0, fun lam _ T H a h hT hH hh hha => ?_⟩
  obtain ⟨A, hA0, hA⟩ := exists_rankin (lam := lam)
  have h16 : (0 : ℝ) < 16 := by norm_num
  have hT0 : 0 < T := by linarith
  set T' := T + H with hT'
  have hTT' : T ≤ T' := by linarith
  set F : ℕ → ℝ → ℂ := fun k t => ((lam (a + 1 + k) * lam (a + 1 + k + h) : ℝ) : ℂ) * rr lam t h (a + 1 + k : ℕ)
    with hF
  set u : ℕ → ℝ := fun k => A * (c2V * Real.exp (4 * ellT T' + 2 * GoodSeq.c lam)) * (((a + 1 + k : ℕ) : ℝ) ^ (-(4 : ℝ))) with hu
  have hus : Summable u := (summable_M4 a).mul_left _
  have hFb : ∀ k t, t ∈ Icc 16 T' → ‖F k t‖ ≤ u k := by
    intro k t ht
    exact norm_F_le hA0 hA h (a + 1 + k) (by omega) (by linarith [ht.1]) ht.2
  have hFc : ∀ k, ContinuousOn (F k) (Icc 16 T') := fun k =>
    continuousOn_const.mul (continuousOn_rr _ _ h16)
  -- identity
  have hzz : ∀ k, zz lam T H (a + k, a + k + h) =
      (∫ t in (16 : ℝ)..T, F k t) + (1 / (H : ℂ)) * ∫ t in T..T', ((T' - t : ℝ) : ℂ) * F k t := by
    intro k
    rw [zz_eq_rr T H (by omega : a + k < a + k + h)]
    have e1 : ((a + k + h : ℕ) : ℝ) - ((a + k : ℕ) : ℝ) = (h : ℝ) := by push_cast; ring
    have e2 : ((a + k : ℕ) : ℝ) + 1 = ((a + 1 + k : ℕ) : ℝ) := by push_cast; ring
    rw [e1, e2, show a + k + 1 = a + 1 + k by ring, show a + k + h + 1 = a + 1 + k + h by ring]
    simp only [hF]
    rw [intervalIntegral.integral_const_mul, ← hT']
    have : (∫ t in T..T', ((T' - t : ℝ) : ℂ) * (((lam (a + 1 + k) * lam (a + 1 + k + h) : ℝ) : ℂ) *
        rr lam t h (a + 1 + k : ℕ))) = ((lam (a + 1 + k) * lam (a + 1 + k + h) : ℝ) : ℂ) *
        ∫ t in T..T', ((T' - t : ℝ) : ℂ) * rr lam t h (a + 1 + k : ℕ) := by
      rw [← intervalIntegral.integral_const_mul]; congr 1; funext t; ring
    rw [this]; ring
  -- summability and interchange
  have hI1 := integral_tsum_Icc hT (fun k => (hFc k).mono (Icc_subset_Icc le_rfl hTT')) hus
    (fun k t ht => hFb k t ⟨ht.1, ht.2.trans hTT'⟩)
  have hG : ∀ k, ContinuousOn (fun t => ((T' - t : ℝ) : ℂ) * F k t) (Icc T T') := fun k =>
    (Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.sub continuousOn_id)).mul
      ((hFc k).mono (Icc_subset_Icc (by linarith) le_rfl))
  have hGb : ∀ k t, t ∈ Icc T T' → ‖((T' - t : ℝ) : ℂ) * F k t‖ ≤ H * u k := by
    intro k t ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
    have := hFb k t ⟨by linarith [ht.1], ht.2⟩
    have : T' - t ≤ H := by linarith [ht.1]
    exact mul_le_mul this (hFb k t ⟨by linarith [ht.1], ht.2⟩) (norm_nonneg _) hH.le
  have hI2 := integral_tsum_Icc hTT' hG (hus.mul_left H) hGb
  have hs1 : Summable fun k => ∫ t in (16 : ℝ)..T, F k t := by
    refine Summable.of_norm_bounded (hus.mul_left (T - 16)) (fun k => ?_)
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := u k) fun t ht => ?_).trans (le_of_eq ?_)
    · rw [uIoc_of_le hT] at ht; exact hFb k t ⟨ht.1.le, ht.2.trans hTT'⟩
    · rw [abs_of_nonneg (by linarith)]; ring
  have hs2 : Summable fun k => ∫ t in T..T', ((T' - t : ℝ) : ℂ) * F k t := by
    refine Summable.of_norm_bounded ((hus.mul_left H).mul_left (T' - T)) (fun k => ?_)
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := H * u k) fun t ht => ?_).trans (le_of_eq ?_)
    · rw [uIoc_of_le hTT'] at ht; exact hGb k t ⟨ht.1.le, ht.2⟩
    · rw [abs_of_nonneg (by linarith)]; ring
  have hsum : Summable (fun k : ℕ => zz lam T H (a + k, a + k + h)) := by
    simp_rw [hzz]; exact hs1.add (hs2.mul_left _)
  refine ⟨hsum, ?_⟩
  simp_rw [hzz]
  rw [hs1.tsum_add (hs2.mul_left _), tsum_mul_left, ← hI1, ← hI2]
  -- pointwise SCS bound
  set β : ℝ := K * (h : ℝ) ^ (1 / 21 : ℝ) * ((a : ℝ) ^ (-(1 / 42 : ℝ)) + T' * h * (a : ℝ) ^ (-(1 + 1 / 42 : ℝ)))
    with hβ
  have hβt : ∀ t ∈ Icc 16 T', ‖∑' k, F k t‖ ≤ β := by
    intro t ht
    have hsF : Summable (F · t) := Summable.of_norm_bounded hus (fun k => hFb k t ht)
    refine (hK lam h a t hh hha (by linarith [ht.1]) hsF).trans ?_
    rw [hβ]
    have : 0 ≤ (a : ℝ) ^ (-(1 + 1 / 42 : ℝ)) := by positivity
    have : t * h * (a : ℝ) ^ (-(1 + 1 / 42 : ℝ)) ≤ T' * h * (a : ℝ) ^ (-(1 + 1 / 42 : ℝ)) := by
      gcongr; exact ht.2
    have : 0 ≤ K * (h : ℝ) ^ (1 / 21 : ℝ) := by positivity
    nlinarith
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans (hβt 16 ⟨le_rfl, by linarith⟩)
  have b1 : ‖∫ t in (16 : ℝ)..T, ∑' k, F k t‖ ≤ β * (T - 16) := by
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := β) fun t ht => ?_).trans (le_of_eq ?_)
    · rw [uIoc_of_le hT] at ht; exact hβt t ⟨ht.1.le, ht.2.trans hTT'⟩
    · rw [abs_of_nonneg (by linarith)]
  have b2 : ‖∫ t in T..T', ∑' k, ((T' - t : ℝ) : ℂ) * F k t‖ ≤ H * β * (T' - T) := by
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := H * β) fun t ht => ?_).trans (le_of_eq ?_)
    · rw [uIoc_of_le hTT'] at ht
      rw [tsum_mul_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
      exact mul_le_mul (by linarith [ht.1]) (hβt t ⟨by linarith [ht.1], ht.2⟩) (norm_nonneg _) hH.le
    · rw [abs_of_nonneg (by linarith)]
  have hHn : ‖1 / (H : ℂ)‖ = 1 / H := by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, hHn]
  have hTH : T' - T = H := by rw [hT']; ring
  rw [hTH] at b2
  calc ‖∫ t in (16 : ℝ)..T, ∑' k, F k t‖ + 1 / H * ‖∫ t in T..T', ∑' k, ((T' - t : ℝ) : ℂ) * F k t‖
      ≤ β * (T - 16) + 1 / H * (H * β * H) := by gcongr
    _ = β * (T - 16 + H) := by field_simp
    _ ≤ β * T' := by gcongr; linarith
    _ = _ := by rw [hβ]; ring

end RamanujanTau.TwistedMoment
