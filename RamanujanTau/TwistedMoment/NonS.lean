/-
# Pointwise majorants for the pair bound, by region

For `q = (m,j)`: `M = m+1`, `h = j+1`, `N = M+h`, `Λ = log MN`, `E = (T+H)/2π`.
`maj q` is the right side of `norm_zz_le` for the pair `(m, m+j+1)`; we split `maj = P1 + P2` and bound
`P2` in the far region `h ≥ M`, and in the near region `h < M` (two ways).
-/
import RamanujanTau.TwistedMoment.Pair

set_option autoImplicit false

namespace RamanujanTau.TwistedMoment

variable {lam : ℕ → ℝ} [GoodSeq lam]

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.ZetaAFE RamanujanTau.GoodSecondTerm RamanujanTau.GoodSecondTerm2

variable (lam) in
/-- `|λ(M)||λ(N)|` for the pair `(m, n)`. -/
noncomputable def ll (m n : ℕ) : ℝ := |lam (m + 1)| * |lam (n + 1)|

lemma ll_nonneg (m n : ℕ) : 0 ≤ ll lam m n := by unfold ll; positivity

noncomputable def Cn : ℝ := 7 * Kphi + 3 * KW

lemma Cn_pos : 0 < Cn := by unfold Cn; have := Kphi_pos; have := KW_pos; positivity

variable (lam) in
/-- First part `P1`. -/
noncomputable def P1 (m n : ℕ) : ℝ :=
  ll lam m n * Real.exp (-((lg m + lg n) / 2)) * (c16 * Real.exp (-(6 * (lg m + lg n))) *
    (((n : ℝ) + 1) / ((n : ℝ) - m)))

variable (lam) in
/-- Second part `P2`. -/
noncomputable def P2 (H T' : ℝ) (m n : ℕ) : ℝ :=
  ll lam m n * Real.exp (-((lg m + lg n) / 2)) * ((((n : ℝ) + 1) / ((n : ℝ) - m)) ^ 2 *
    (7 * Kphi * Real.exp (-((lg m + lg n) / 2)) * Dfac (lg m + lg n) T' + 3 * KW * Dfac (lg m + lg n) T' / H))

lemma norm_zz_le' {T H : ℝ} (hT : 16 ≤ T) (hH : 0 < H) {m n : ℕ} (hmn : m < n) :
    ‖zz lam T H (m, n)‖ ≤ Real.exp (6 * GoodSeq.c lam) *
      (P1 lam m n + P2 lam H ((T + H) * Real.exp (GoodSeq.c lam / 2)) m n) := by
  have := norm_zz_le (lam := lam) hT hH hmn
  unfold P1 P2 ll; linarith [this]

lemma exp_lg (m : ℕ) : Real.exp (lg m) = (m : ℝ) + 1 := by unfold lg; exact Real.exp_log (by positivity)

lemma exp_neg_s_lg (s : ℝ) (m : ℕ) : Real.exp (-(s * lg m)) = ((m : ℝ) + 1) ^ (-s) := by
  unfold lg; rw [Real.rpow_def_of_pos (by positivity)]; ring_nf

lemma P1_le (m n : ℕ) (hmn : m < n) :
    P1 lam m n ≤ c16 * (|lam (m + 1)| * ((m : ℝ) + 1) ^ (-(13 / 2 : ℝ))) *
      (|lam (n + 1)| * ((n : ℝ) + 1) ^ (-(11 / 2 : ℝ))) := by
  unfold P1 ll
  have hm : (m : ℝ) < n := by exact_mod_cast hmn
  have hd : (1 : ℝ) ≤ (n : ℝ) - m := by
    have : m + 1 ≤ n := hmn
    have : ((m + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast this
    push_cast at this; linarith
  have hq : ((n : ℝ) + 1) / ((n : ℝ) - m) ≤ (n : ℝ) + 1 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have e : Real.exp (-((lg m + lg n) / 2)) * Real.exp (-(6 * (lg m + lg n))) * ((n : ℝ) + 1) =
      ((m : ℝ) + 1) ^ (-(13 / 2 : ℝ)) * ((n : ℝ) + 1) ^ (-(11 / 2 : ℝ)) := by
    conv_lhs => rw [← exp_lg n]
    rw [← Real.exp_add, ← Real.exp_add,
      show -((lg m + lg n) / 2) + -(6 * (lg m + lg n)) + lg n = -(13 / 2 * lg m) + -(11 / 2 * lg n) by ring,
      Real.exp_add, exp_neg_s_lg, exp_neg_s_lg]
  have hc := c16_pos
  have h0 : 0 ≤ |lam (m + 1)| * |lam (n + 1)| := by positivity
  calc |lam (m + 1)| * |lam (n + 1)| * Real.exp (-((lg m + lg n) / 2)) *
        (c16 * Real.exp (-(6 * (lg m + lg n))) * (((n : ℝ) + 1) / ((n : ℝ) - m)))
      ≤ |lam (m + 1)| * |lam (n + 1)| * Real.exp (-((lg m + lg n) / 2)) *
        (c16 * Real.exp (-(6 * (lg m + lg n))) * ((n : ℝ) + 1)) := by gcongr
    _ = c16 * |lam (m + 1)| * |lam (n + 1)| *
        (Real.exp (-((lg m + lg n) / 2)) * Real.exp (-(6 * (lg m + lg n))) * ((n : ℝ) + 1)) := by ring
    _ = _ := by rw [e]; ring

lemma Dfac_le_exp {a : ℝ} (ha0 : 0 ≤ a) (ha2 : a ≤ 2) (Λ T' : ℝ) :
    Dfac Λ T' ≤ Real.exp (-(a * (Λ - 2 * ellT T'))) := by
  unfold Dfac
  rcases le_total 0 (Λ - 2 * ellT T') with h | h
  · refine (min_le_right _ _).trans (Real.exp_le_exp.mpr ?_); nlinarith
  · refine (min_le_left _ _).trans (Real.one_le_exp ?_); nlinarith

/-- Far region `h ≥ M`, i.e. `2m + 1 ≤ n`. -/
lemma P2_far {H T' s : ℝ} (hH : 0 < H) (hs0 : 0 ≤ s) (hs : s ≤ 3 / 2) {m n : ℕ} (hfar : 2 * m + 1 ≤ n) :
    P2 lam H T' m n ≤ 4 * (7 * Kphi * Real.exp (2 * s * ellT T') + 3 * KW / H * Real.exp ((1 + 2 * s) * ellT T')) *
      ((|lam (m + 1)| * ((m : ℝ) + 1) ^ (-(1 + s))) * (|lam (n + 1)| * ((n : ℝ) + 1) ^ (-(1 + s)))) := by
  unfold P2 ll
  have hq : (((n : ℝ) + 1) / ((n : ℝ) - m)) ^ 2 ≤ 4 := by
    have h1 : ((2 * m + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hfar
    push_cast at h1
    have hpos : (0 : ℝ) < (n : ℝ) - m := by linarith [Nat.cast_nonneg (α := ℝ) m]
    have h2 : ((n : ℝ) + 1) / ((n : ℝ) - m) ≤ 2 := by rw [div_le_iff₀ hpos]; linarith
    have h3 : 0 ≤ ((n : ℝ) + 1) / ((n : ℝ) - m) := by positivity
    nlinarith
  have hD1 := Dfac_le_exp (a := s) hs0 (by linarith) (lg m + lg n) T'
  have hD2 := Dfac_le_exp (a := 1 / 2 + s) (by linarith) (by linarith) (lg m + lg n) T'
  have hD0 := Dfac_nonneg (lg m + lg n) T'
  have hK := Kphi_pos
  have hKW := KW_pos
  have e1 : Real.exp (-((lg m + lg n) / 2)) * (Real.exp (-((lg m + lg n) / 2)) *
      Real.exp (-(s * ((lg m + lg n) - 2 * ellT T')))) =
      Real.exp (2 * s * ellT T') * (((m : ℝ) + 1) ^ (-(1 + s)) * ((n : ℝ) + 1) ^ (-(1 + s))) := by
    rw [← exp_neg_s_lg, ← exp_neg_s_lg]; simp only [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (-((lg m + lg n) / 2)) * Real.exp (-((1 / 2 + s) * ((lg m + lg n) - 2 * ellT T'))) =
      Real.exp ((1 + 2 * s) * ellT T') * (((m : ℝ) + 1) ^ (-(1 + s)) * ((n : ℝ) + 1) ^ (-(1 + s))) := by
    rw [← exp_neg_s_lg, ← exp_neg_s_lg]; simp only [← Real.exp_add]; congr 1; ring
  have hll : 0 ≤ |lam (m + 1)| * |lam (n + 1)| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hE : 0 ≤ Real.exp (-((lg m + lg n) / 2)) := (Real.exp_pos _).le
  have hin : 7 * Kphi * Real.exp (-((lg m + lg n) / 2)) * Dfac (lg m + lg n) T' + 3 * KW * Dfac (lg m + lg n) T' / H ≤
      7 * Kphi * Real.exp (-((lg m + lg n) / 2)) * Real.exp (-(s * ((lg m + lg n) - 2 * ellT T'))) +
        3 * KW * Real.exp (-((1 / 2 + s) * ((lg m + lg n) - 2 * ellT T'))) / H := by
    gcongr
  have hin0 : 0 ≤ 7 * Kphi * Real.exp (-((lg m + lg n) / 2)) * Dfac (lg m + lg n) T' +
      3 * KW * Dfac (lg m + lg n) T' / H :=
    add_nonneg (mul_nonneg (mul_nonneg (by linarith) hE) hD0) (div_nonneg (mul_nonneg (by linarith) hD0) hH.le)
  calc |lam (m + 1)| * |lam (n + 1)| * Real.exp (-((lg m + lg n) / 2)) *
        ((((n : ℝ) + 1) / ((n : ℝ) - m)) ^ 2 *
          (7 * Kphi * Real.exp (-((lg m + lg n) / 2)) * Dfac (lg m + lg n) T' + 3 * KW * Dfac (lg m + lg n) T' / H))
      ≤ |lam (m + 1)| * |lam (n + 1)| * Real.exp (-((lg m + lg n) / 2)) *
        (4 * (7 * Kphi * Real.exp (-((lg m + lg n) / 2)) * Real.exp (-(s * ((lg m + lg n) - 2 * ellT T'))) +
          3 * KW * Real.exp (-((1 / 2 + s) * ((lg m + lg n) - 2 * ellT T'))) / H)) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hll hE)
        exact mul_le_mul hq hin hin0 (by norm_num)
    _ = 4 * (|lam (m + 1)| * |lam (n + 1)|) * (7 * Kphi * (Real.exp (-((lg m + lg n) / 2)) *
          (Real.exp (-((lg m + lg n) / 2)) * Real.exp (-(s * ((lg m + lg n) - 2 * ellT T'))))) +
          3 * KW / H * (Real.exp (-((lg m + lg n) / 2)) *
          Real.exp (-((1 / 2 + s) * ((lg m + lg n) - 2 * ellT T'))))) := by ring
    _ = _ := by rw [e1, e2]; ring

/-- Near region `h < M`: `P2 ≤ ll lam (4/h²) D₀ (7Kφ + 3K_W M/H)`, `D₀ = min(1, E⁴/M⁴)`. -/
lemma P2_near {H T' : ℝ} (hH : 0 < H) {m n : ℕ} (hmn : m < n) (hnear : n < 2 * m + 1) :
    P2 lam H T' m n ≤ ll lam m n * (4 / ((n : ℝ) - m) ^ 2) *
      min 1 (Real.exp (ellT T') ^ 4 / ((m : ℝ) + 1) ^ 4) * (7 * Kphi + 3 * KW * (((m : ℝ) + 1) / H)) := by
  unfold P2
  set M : ℝ := (m : ℝ) + 1 with hM
  set E : ℝ := Real.exp (ellT T') with hEdef
  have hM1 : 1 ≤ M := by rw [hM]; linarith [Nat.cast_nonneg (α := ℝ) m]
  have hmr : (m : ℝ) < n := by exact_mod_cast hmn
  have hh : (0 : ℝ) < (n : ℝ) - m := by linarith
  have hnr : ((n : ℝ) + 1) ≤ 2 * M := by
    have : n + 1 ≤ 2 * m + 1 := hnear
    have : ((n + 1 : ℕ) : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this; rw [hM]; linarith
  have hNM : M ≤ (n : ℝ) + 1 := by rw [hM]; linarith
  have hll := ll_nonneg (lam := lam) m n
  have hK := Kphi_pos
  have hKW := KW_pos
  -- e^{-Λ/2} ≤ 1/M
  have hE2 : Real.exp (-((lg m + lg n) / 2)) ≤ 1 / M := by
    have : Real.exp (-((lg m + lg n) / 2)) * Real.exp (-((lg m + lg n) / 2)) = 1 / (M * ((n : ℝ) + 1)) := by
      rw [← Real.exp_add, show -((lg m + lg n) / 2) + -((lg m + lg n) / 2) = -(lg m + lg n) by ring,
        Real.exp_neg, Real.exp_add, exp_lg, exp_lg, hM, one_div]
    have hpos := Real.exp_pos (-((lg m + lg n) / 2))
    have h2 : 1 / (M * ((n : ℝ) + 1)) ≤ (1 / M) ^ 2 := by
      rw [div_pow, one_pow, one_div_le_one_div (by positivity) (by positivity)]; nlinarith
    have h3 : 0 ≤ 1 / M := by positivity
    nlinarith
  have hE0 : 0 ≤ Real.exp (-((lg m + lg n) / 2)) := (Real.exp_pos _).le
  -- D ≤ D₀
  have hD : Dfac (lg m + lg n) T' ≤ min 1 (E ^ 4 / M ^ 4) := by
    unfold Dfac
    apply min_le_min le_rfl
    have : Real.exp (-(2 * (lg m + lg n - 2 * ellT T'))) = E ^ 4 / (M * ((n : ℝ) + 1)) ^ 2 := by
      have e4 : Real.exp (4 * ellT T') = E ^ 4 := by
        rw [hEdef, ← Real.exp_nat_mul]; norm_num
      have e2 : Real.exp (2 * (lg m + lg n)) = (M * ((n : ℝ) + 1)) ^ 2 := by
        rw [show 2 * (lg m + lg n) = ((2 : ℕ) : ℝ) * (lg m + lg n) by norm_num, Real.exp_nat_mul,
          Real.exp_add, exp_lg, exp_lg, hM]
      rw [show -(2 * (lg m + lg n - 2 * ellT T')) = 4 * ellT T' - 2 * (lg m + lg n) by ring,
        Real.exp_sub, e4, e2]
    rw [this]
    gcongr
    rw [show M ^ 4 = (M * M) ^ 2 by ring]
    gcongr
  have hD0 := Dfac_nonneg (lg m + lg n) T'
  have hq : ((n : ℝ) + 1) / ((n : ℝ) - m) ≤ 2 * M / ((n : ℝ) - m) := by gcongr
  have hq0 : 0 ≤ ((n : ℝ) + 1) / ((n : ℝ) - m) := by positivity
  have hmin0 : 0 ≤ min 1 (E ^ 4 / M ^ 4) := le_min zero_le_one (by positivity)
  calc ll lam m n * Real.exp (-((lg m + lg n) / 2)) * ((((n : ℝ) + 1) / ((n : ℝ) - m)) ^ 2 *
        (7 * Kphi * Real.exp (-((lg m + lg n) / 2)) * Dfac (lg m + lg n) T' + 3 * KW * Dfac (lg m + lg n) T' / H))
      ≤ ll lam m n * (1 / M) * ((2 * M / ((n : ℝ) - m)) ^ 2 *
        (7 * Kphi * (1 / M) * min 1 (E ^ 4 / M ^ 4) + 3 * KW * min 1 (E ^ 4 / M ^ 4) / H)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hE2 hll) _ (by
          apply mul_nonneg (sq_nonneg _)
          exact add_nonneg (mul_nonneg (mul_nonneg (by linarith) hE0) hD0)
            (div_nonneg (mul_nonneg (by linarith) hD0) hH.le)) (mul_nonneg hll (by positivity))
        apply mul_le_mul (pow_le_pow_left₀ hq0 hq 2) _ (add_nonneg (mul_nonneg (mul_nonneg (by linarith) hE0) hD0)
            (div_nonneg (mul_nonneg (by linarith) hD0) hH.le)) (sq_nonneg _)
        apply add_le_add
        · exact mul_le_mul (mul_le_mul_of_nonneg_left hE2 (by linarith)) hD hD0
            (mul_nonneg (by linarith) (by positivity))
        · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hD (by linarith)) hH.le
    _ = _ := by
        have hM0 : M ≠ 0 := by linarith
        field_simp
        ring

lemma P2_nearM {H T' : ℝ} (hH : 0 < H) {m n : ℕ} (hmn : m < n) (hnear : n < 2 * m + 1)
    (hMH : (m : ℝ) + 1 ≤ H) :
    P2 lam H T' m n ≤ ll lam m n * (4 / ((n : ℝ) - m) ^ 2) * Cn := by
  refine (P2_near hH hmn hnear).trans ?_
  have hll := ll_nonneg (lam := lam) m n
  have h1 : min 1 (Real.exp (ellT T') ^ 4 / ((m : ℝ) + 1) ^ 4) ≤ 1 := min_le_left _ _
  have h0 : 0 ≤ min 1 (Real.exp (ellT T') ^ 4 / ((m : ℝ) + 1) ^ 4) := le_min zero_le_one (by positivity)
  have h2 : 7 * Kphi + 3 * KW * (((m : ℝ) + 1) / H) ≤ Cn := by
    unfold Cn; have := KW_pos
    have : ((m : ℝ) + 1) / H ≤ 1 := by rw [div_le_one hH]; exact hMH
    nlinarith
  have h3 : 0 ≤ 7 * Kphi + 3 * KW * (((m : ℝ) + 1) / H) := by
    have := Kphi_pos; have := KW_pos; positivity
  have h4 : 0 ≤ ll lam m n * (4 / ((n : ℝ) - m) ^ 2) := mul_nonneg hll (by positivity)
  calc ll lam m n * (4 / ((n : ℝ) - m) ^ 2) * min 1 (Real.exp (ellT T') ^ 4 / ((m : ℝ) + 1) ^ 4) *
        (7 * Kphi + 3 * KW * (((m : ℝ) + 1) / H))
      ≤ ll lam m n * (4 / ((n : ℝ) - m) ^ 2) * 1 * Cn := by gcongr
    _ = _ := by ring

lemma minpow_le {E M ε : ℝ} (hE : 0 < E) (hM : 0 < M) (hε0 : 0 ≤ ε) (hε : ε ≤ 2) :
    min 1 ((E / M) ^ 3) ≤ (E / M) ^ (1 + ε) := by
  have hy : 0 < E / M := by positivity
  rcases le_total (E / M) 1 with h | h
  · refine (min_le_right _ _).trans ?_
    rw [show (E / M) ^ 3 = (E / M) ^ ((3 : ℕ) : ℝ) by rw [Real.rpow_natCast]]
    exact Real.rpow_le_rpow_of_exponent_ge hy h (by push_cast; linarith)
  · exact (min_le_left _ _).trans (Real.one_le_rpow h (by linarith))

lemma P2_nearH {H T' ε : ℝ} (hH : 0 < H) (hε0 : 0 ≤ ε) (hε : ε ≤ 2) {m n : ℕ} (hmn : m < n)
    (hnear : n < 2 * m + 1) :
    P2 lam H T' m n ≤ ll lam m n * (4 / ((n : ℝ) - m) ^ 2) * (Cn * (1 + Real.exp (ellT T') / H) *
      (Real.exp (ellT T') ^ (1 + ε) * ((m : ℝ) + 1) ^ (-(1 + ε)))) := by
  refine (P2_near hH hmn hnear).trans ?_
  set M : ℝ := (m : ℝ) + 1 with hM
  set E : ℝ := Real.exp (ellT T') with hEdef
  have hM0 : 0 < M := by rw [hM]; positivity
  have hE0 : 0 < E := Real.exp_pos _
  have hll := ll_nonneg (lam := lam) m n
  have hK := Kphi_pos
  have hKW := KW_pos
  have hkey : min 1 (E ^ 4 / M ^ 4) * (7 * Kphi + 3 * KW * (M / H)) ≤
      Cn * (1 + E / H) * min 1 ((E / M) ^ 3) := by
    have h1 : 7 * Kphi + 3 * KW * (M / H) ≤ Cn * (1 + M / H) := by
      unfold Cn; have : 0 ≤ M / H := by positivity
      nlinarith
    have hCn := Cn_pos
    have h2 : min 1 (E ^ 4 / M ^ 4) * (1 + M / H) ≤ (1 + E / H) * min 1 ((E / M) ^ 3) := by
      rcases le_total M E with h | h
      · have : min 1 ((E / M) ^ 3) = 1 := min_eq_left (by
          have : 1 ≤ E / M := by rw [le_div_iff₀ hM0]; linarith
          exact one_le_pow₀ this)
        rw [this]
        have ha : M / H ≤ E / H := by gcongr
        have hb : min 1 (E ^ 4 / M ^ 4) ≤ 1 := min_le_left _ _
        have hc : 0 ≤ 1 + M / H := by positivity
        calc min 1 (E ^ 4 / M ^ 4) * (1 + M / H) ≤ 1 * (1 + M / H) := mul_le_mul_of_nonneg_right hb hc
          _ ≤ (1 + E / H) * 1 := by linarith
      · have hy : E / M ≤ 1 := by rw [div_le_one hM0]; exact h
        have hy0 : 0 ≤ E / M := by positivity
        have : min 1 ((E / M) ^ 3) = (E / M) ^ 3 := min_eq_right (by
          calc (E / M) ^ 3 ≤ 1 ^ 3 := pow_le_pow_left₀ hy0 hy 3
            _ = 1 := by norm_num)
        rw [this]
        have hm4 : min 1 (E ^ 4 / M ^ 4) ≤ (E / M) ^ 4 := by rw [div_pow]; exact min_le_right _ _
        have e : (E / M) ^ 4 * (1 + M / H) = (E / M) ^ 3 * (E / M + E / H) := by field_simp
        have : (E / M) ^ 3 * (E / M + E / H) ≤ (1 + E / H) * (E / M) ^ 3 := by
          have := pow_nonneg hy0 3; nlinarith
        have h0 : 0 ≤ 1 + M / H := by positivity
        calc min 1 (E ^ 4 / M ^ 4) * (1 + M / H) ≤ (E / M) ^ 4 * (1 + M / H) := by gcongr
          _ = _ := e
          _ ≤ _ := this
    have h0 : 0 ≤ min 1 (E ^ 4 / M ^ 4) := le_min zero_le_one (by positivity)
    calc min 1 (E ^ 4 / M ^ 4) * (7 * Kphi + 3 * KW * (M / H)) ≤ min 1 (E ^ 4 / M ^ 4) * (Cn * (1 + M / H)) := by
          gcongr
      _ = Cn * (min 1 (E ^ 4 / M ^ 4) * (1 + M / H)) := by ring
      _ ≤ Cn * ((1 + E / H) * min 1 ((E / M) ^ 3)) := by gcongr
      _ = _ := by ring
  have hmp := minpow_le hE0 hM0 hε0 hε
  have hdiv : (E / M) ^ (1 + ε) = E ^ (1 + ε) * M ^ (-(1 + ε)) := by
    rw [Real.div_rpow hE0.le hM0.le, Real.rpow_neg hM0.le, div_eq_mul_inv]
  have h4 : 0 ≤ ll lam m n * (4 / ((n : ℝ) - m) ^ 2) := mul_nonneg hll (by positivity)
  have hC1 : 0 ≤ Cn * (1 + E / H) := by have := Cn_pos; positivity
  calc ll lam m n * (4 / ((n : ℝ) - m) ^ 2) * min 1 (E ^ 4 / M ^ 4) * (7 * Kphi + 3 * KW * (M / H))
      = ll lam m n * (4 / ((n : ℝ) - m) ^ 2) * (min 1 (E ^ 4 / M ^ 4) * (7 * Kphi + 3 * KW * (M / H))) := by ring
    _ ≤ ll lam m n * (4 / ((n : ℝ) - m) ^ 2) * (Cn * (1 + E / H) * min 1 ((E / M) ^ 3)) := by gcongr
    _ ≤ ll lam m n * (4 / ((n : ℝ) - m) ^ 2) * (Cn * (1 + E / H) * (E / M) ^ (1 + ε)) := by gcongr
    _ = _ := by rw [hdiv]

end RamanujanTau.TwistedMoment
