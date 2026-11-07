/-
# The (symmetrised) twisted second moment of `L(Δ, s)`, unconditionally

For `h, k ≥ 1` and `X ≥ 2^{300}`, `H = X^{299/300}`:

    (1/H) ∫_X^{X+H} ∫_{16}^u |L(Δ,6+it)|² ((h/k)^{it} + (k/h)^{it}) dt du
      = MainTw(h,k,X,H) + O((hk)^{33} X^{599/600}),

`MainTw = 2√(hk) Σ_m ι_k(m+1) ι_h(m+1) (m+1)^{−1} P̃(2 log(m+1) − log hk, 0, X, H)` (the smoothed
diagonal `kM = hN`; for coprime `h, k` it is `(2/√(hk)) Σ_r λ(hr)λ(kr) r^{−1} P̃(log(hk r²) …)`).
-/
import RamanujanTau.TwistedMoment.GAvg
import RamanujanTau.GoodSecondTerm.Main

set_option autoImplicit false

namespace RamanujanTau.TwistedMoment

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.ZetaAFE RamanujanTau.GoodSecondTerm RamanujanTau.GoodSecondTerm2 RamanujanTau.HeckeL
open scoped Interval

/-- The twist `(h/k)^{it}`. -/
noncomputable def ph (h k : ℕ) (t : ℝ) : ℂ := cexp (t * I * ((Real.log h - Real.log k : ℝ) : ℂ))

lemma norm_ph (h k : ℕ) (t : ℝ) : ‖ph h k t‖ = 1 := by
  unfold ph
  rw [Complex.norm_exp]
  have : (t * I * ((Real.log h - Real.log k : ℝ) : ℂ)).re = 0 := by
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im]
    ring
  rw [this, Real.exp_zero]

lemma continuous_ph (h k : ℕ) : Continuous (ph h k) := by unfold ph; fun_prop

lemma sq_le_of_sum {a : ℕ → ℝ} {A : ℝ} (ha0 : a 0 = 0) (h : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, a n ^ 2 ≤ A * N)
    (n : ℕ) : a n ^ 2 ≤ A * n := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; simp [ha0]
  · refine le_trans ?_ (h n)
    exact Finset.single_le_sum (f := fun x => a x ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_Icc.2 ⟨h0, le_rfl⟩)

lemma mul_exp_le {a b : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A) (ha : ∀ n, a n ^ 2 ≤ A * n) (hb : ∀ n, b n ^ 2 ≤ A * n)
    (q : ℕ × ℕ) : |a (q.1 + 1) * b (q.2 + 1)| * Real.exp (-((lg q.1 + lg q.2) / 2)) ≤ A := by
  have hx : (0 : ℝ) < (q.1 : ℝ) + 1 := by positivity
  have hy : (0 : ℝ) < (q.2 : ℝ) + 1 := by positivity
  have h1 : |a (q.1 + 1)| ≤ Real.sqrt (A * ((q.1 : ℝ) + 1)) :=
    Real.abs_le_sqrt (by have := ha (q.1 + 1); push_cast at this; exact this)
  have h2 : |b (q.2 + 1)| ≤ Real.sqrt (A * ((q.2 : ℝ) + 1)) :=
    Real.abs_le_sqrt (by have := hb (q.2 + 1); push_cast at this; exact this)
  have hs : Real.sqrt (A * ((q.1 : ℝ) + 1)) * Real.sqrt (A * ((q.2 : ℝ) + 1)) =
      A * Real.sqrt (((q.1 : ℝ) + 1) * ((q.2 : ℝ) + 1)) := by
    rw [← Real.sqrt_mul (by positivity), show A * ((q.1 : ℝ) + 1) * (A * ((q.2 : ℝ) + 1)) =
      A ^ 2 * (((q.1 : ℝ) + 1) * ((q.2 : ℝ) + 1)) by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq hA]
  have he : Real.sqrt (((q.1 : ℝ) + 1) * ((q.2 : ℝ) + 1)) * Real.exp (-((lg q.1 + lg q.2) / 2)) = 1 := by
    unfold lg
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity), Real.log_mul hx.ne' hy.ne', ← Real.exp_add,
      show (Real.log ((q.1 : ℝ) + 1) + Real.log ((q.2 : ℝ) + 1)) * (1 / 2) +
        -((Real.log ((q.1 : ℝ) + 1) + Real.log ((q.2 : ℝ) + 1)) / 2) = 0 by ring, Real.exp_zero]
  rw [abs_mul]
  calc |a (q.1 + 1)| * |b (q.2 + 1)| * Real.exp (-((lg q.1 + lg q.2) / 2))
      ≤ Real.sqrt (A * ((q.1 : ℝ) + 1)) * Real.sqrt (A * ((q.2 : ℝ) + 1)) * Real.exp (-((lg q.1 + lg q.2) / 2)) := by
        gcongr
    _ = A * (Real.sqrt (((q.1 : ℝ) + 1) * ((q.2 : ℝ) + 1)) * Real.exp (-((lg q.1 + lg q.2) / 2))) := by
        rw [hs]; ring
    _ = A := by rw [he, mul_one]

lemma norm_bG2_le' {a b : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A) (ha : ∀ n, a n ^ 2 ≤ A * n) (hb : ∀ n, b n ^ 2 ≤ A * n)
    {t : ℝ} (ht : 16 ≤ t) (c : ℝ) (q : ℕ × ℕ) :
    ‖bG2 a b c t q‖ ≤ A * (c2V * Real.exp (4 * ellT t + 2 * c)) *
      (((q.1 : ℝ) + 1) ^ (-(2 : ℝ)) * ((q.2 : ℝ) + 1) ^ (-(2 : ℝ))) := by
  have hl := mul_exp_le hA ha hb q
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
      c2V * Real.exp (4 * ellT t + 2 * c) * (((q.1 : ℝ) + 1) ^ (-(2 : ℝ)) * ((q.2 : ℝ) + 1) ^ (-(2 : ℝ))) := by
    refine (V_le_exp_k (k := 2) (by norm_num) _).trans (le_of_eq ?_)
    unfold c2V lg
    rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (by positivity), ← Real.exp_add,
      mul_assoc, ← Real.exp_add]
    congr 2; ring
  calc |a (q.1 + 1) * b (q.2 + 1)| * (Real.exp (-((lg q.1 + lg q.2) / 2)) * V (lg q.1 + lg q.2 - c - 2 * ellT t))
      = (|a (q.1 + 1) * b (q.2 + 1)| * Real.exp (-((lg q.1 + lg q.2) / 2))) *
        V (lg q.1 + lg q.2 - c - 2 * ellT t) := by ring
    _ ≤ A * (c2V * Real.exp (4 * ellT t + 2 * c) *
        (((q.1 : ℝ) + 1) ^ (-(2 : ℝ)) * ((q.2 : ℝ) + 1) ^ (-(2 : ℝ)))) := mul_le_mul hl hV hV0 hA
    _ = _ := by ring

lemma summable_bG2 {a b : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A) (ha : ∀ n, a n ^ 2 ≤ A * n) (hb : ∀ n, b n ^ 2 ≤ A * n)
    {t : ℝ} (ht : 16 ≤ t) (c : ℝ) : Summable (bG2 a b c t) := by
  refine Summable.of_norm_bounded (Summable.mul_left _ ?_) (fun q => norm_bG2_le' hA ha hb ht c q)
  exact Summable.mul_of_nonneg (summable_shift_rpow (s := 2) (by norm_num))
    (summable_shift_rpow (s := 2) (by norm_num)) (fun n => by positivity) (fun n => by positivity)

lemma iota_sq_le {a : ℕ} (ha : 1 ≤ a) (n : ℕ) : iota a n ^ 2 ≤ Arank * n :=
  sq_le_of_sum (iota_zero a) (fun N => Arank_spec a N ha) n

/-- **Twisted pointwise identity** (`t ≥ 16`). -/
theorem twist_pointwise {h k : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k) {r : ℝ} (hr : r ≠ 0)
    (hgp : ∀ n, gS h k 1 r n ^ 2 ≤ C1 * n) (hgm : ∀ n, gS h k (-1) r n ^ 2 ≤ C1 * n) {t : ℝ} (ht : 16 ≤ t) :
    (∑' p, bD t (2 * ellT t) p) * (ph h k t + ph k h t) =
      ((Real.sqrt ((h * k : ℕ) : ℝ) / (2 * r ^ 2) : ℝ) : ℂ) *
        (∑' q, bG2 (gS h k 1 r) (gS h k 1 r) (Real.log ((h * k : ℕ) : ℝ)) t q -
          ∑' q, bG2 (gS h k (-1) r) (gS h k (-1) r) (Real.log ((h * k : ℕ) : ℝ)) t q) := by
  set c := Real.log ((h * k : ℕ) : ℝ) with hc
  unfold ph
  rw [mul_add, twist_reindex hh hk t, twist_reindex hk hh t, Nat.mul_comm k h, ← hc, ← mul_add]
  have hA := Arank_nonneg
  have s1 := summable_bG2 hA (iota_sq_le hk) (iota_sq_le hh) ht c
  have s2 := summable_bG2 hA (iota_sq_le hh) (iota_sq_le hk) ht c
  have s3 := summable_bG2 C1_pos.le hgp hgp ht c
  have s4 := summable_bG2 C1_pos.le hgm hgm ht c
  rw [← s1.tsum_add s2, tsum_congr (fun q => polarise (iota k) (iota h) hr c t q), tsum_mul_left]
  rw [show (fun q => bG2 (fun n => r * (iota k n + 1 * iota h n)) (fun n => r * (iota k n + 1 * iota h n)) c t q -
      bG2 (fun n => r * (iota k n + (-1) * iota h n)) (fun n => r * (iota k n + (-1) * iota h n)) c t q) =
      fun q => bG2 (gS h k 1 r) (gS h k 1 r) c t q - bG2 (gS h k (-1) r) (gS h k (-1) r) c t q from rfl]
  rw [s3.tsum_sub s4]
  push_cast
  ring

/-! ### The averaging operator -/

/-- `Av F = (1/H) ∫_X^{X+H} ∫_{16}^u F`. -/
noncomputable def Av (X H : ℝ) (F : ℝ → ℂ) : ℂ := (1 / (H : ℂ)) * ∫ u in X..X + H, ∫ t in (16 : ℝ)..u, F t

lemma Av_add {X H : ℝ} (hX : 16 ≤ X) (hH : 0 < H) {F G : ℝ → ℂ} (hF : ContinuousOn F (Icc 16 (X + H)))
    (hG : ContinuousOn G (Icc 16 (X + H))) : Av X H (fun t => F t + G t) = Av X H F + Av X H G := by
  unfold Av
  rw [← mul_add]
  congr 1
  have hFi : ∀ u ∈ Icc X (X + H), IntervalIntegrable F volume 16 u := fun u hu =>
    (hF.mono (Icc_subset_Icc le_rfl hu.2)).intervalIntegrable_of_Icc (by linarith [hu.1])
  have hGi : ∀ u ∈ Icc X (X + H), IntervalIntegrable G volume 16 u := fun u hu =>
    (hG.mono (Icc_subset_Icc le_rfl hu.2)).intervalIntegrable_of_Icc (by linarith [hu.1])
  have hXH : X ≤ X + H := by linarith
  rw [intervalIntegral.integral_congr (g := fun u => (∫ t in (16 : ℝ)..u, F t) + ∫ t in (16 : ℝ)..u, G t)
    (fun u hu => by
      rw [uIcc_of_le hXH] at hu
      exact intervalIntegral.integral_add (hFi u hu) (hGi u hu))]
  have hP : ∀ (K : ℝ → ℂ), ContinuousOn K (Icc 16 (X + H)) →
      IntervalIntegrable (fun u => ∫ t in (16 : ℝ)..u, K t) volume X (X + H) := by
    intro K hK
    have hKi : IntervalIntegrable K volume 16 (X + H) := hK.intervalIntegrable_of_Icc (by linarith)
    have := intervalIntegral.continuousOn_primitive_interval' hKi (left_mem_uIcc)
    refine (this.mono ?_).intervalIntegrable
    rw [uIcc_of_le hXH, uIcc_of_le (by linarith : (16 : ℝ) ≤ X + H)]
    exact Icc_subset_Icc hX le_rfl
  exact intervalIntegral.integral_add (hP F hF) (hP G hG)

lemma Av_smul (X H : ℝ) (a : ℂ) (F : ℝ → ℂ) : Av X H (fun t => a * F t) = a * Av X H F := by
  unfold Av
  simp_rw [intervalIntegral.integral_const_mul]
  ring

lemma norm_Av_le {X H : ℝ} (hH : 0 < H) {F : ℝ → ℂ} {B : ℝ}
    (hb : ∀ u ∈ Icc X (X + H), ‖∫ t in (16 : ℝ)..u, F t‖ ≤ B) : ‖Av X H F‖ ≤ B := by
  unfold Av
  have hXH : X ≤ X + H := by linarith
  have h1 : ‖∫ u in X..X + H, ∫ t in (16 : ℝ)..u, F t‖ ≤ B * |X + H - X| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => by
      rw [uIoc_of_le hXH] at hu; exact hb u ⟨hu.1.le, hu.2⟩
  rw [show X + H - X = H by ring, abs_of_pos hH] at h1
  rw [norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
  calc 1 / H * ‖∫ u in X..X + H, ∫ t in (16 : ℝ)..u, F t‖ ≤ 1 / H * (B * H) := by gcongr
    _ = B := by field_simp

/-- The main term: the smoothed diagonal `kM = hN`. -/
noncomputable def MainTw (h k : ℕ) (X H : ℝ) : ℂ :=
  2 * (Real.sqrt ((h * k : ℕ) : ℝ) : ℂ) * ∑' m : ℕ,
    ((iota k (m + 1) * iota h (m + 1) * Real.exp (-((lg m + lg m) / 2)) : ℝ) : ℂ) *
      Ptil (lg m + lg m - Real.log ((h * k : ℕ) : ℝ)) (lg m - lg m) X H

/-- The twisted moment, averaged. -/
noncomputable def TwAv (h k : ℕ) (X H : ℝ) : ℂ :=
  Av X H (fun t => ((‖tauL (6 + t * I)‖ ^ 2 : ℝ) : ℂ) * (ph h k t + ph k h t))

end RamanujanTau.TwistedMoment
