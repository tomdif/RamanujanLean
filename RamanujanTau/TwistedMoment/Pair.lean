/-
# The averaged off-diagonal pair term for a generic sequence

`zz lam T H p = coefG p · Ptil(Λ_p − c, λ_p, T, H)` for `p.1 ≠ p.2`, with
`coefG p = λ(M)λ(N)e^{−Λ/2}`, `Λ = log MN`, `λ = log(N/M)`, `c = GoodSeq.c lam`.

`norm_zz_le`: the bound of `GoodSecondTerm2.norm_zz_le` with an extra factor `e^{6c}` and
`T+H` replaced by `T'' = (T+H)e^{c/2}` inside `Dfac`.
-/
import RamanujanTau.TwistedMoment.SCSAbel

set_option autoImplicit false

namespace RamanujanTau.TwistedMoment

variable {lam : ℕ → ℝ} [GoodSeq lam]

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.ZetaAFE RamanujanTau.GoodSecondTerm RamanujanTau.GoodSecondTerm2

variable (lam) in
/-- The pair coefficient `λ(M)λ(N)(MN)^{−1/2}`. -/
noncomputable def coefG (p : ℕ × ℕ) : ℝ := lam (p.1 + 1) * lam (p.2 + 1) * Real.exp (-((lg p.1 + lg p.2) / 2))

variable (lam) in
/-- The averaged pair term. -/
noncomputable def zz (T H : ℝ) (p : ℕ × ℕ) : ℂ :=
  if p.1 = p.2 then 0 else (coefG lam p : ℂ) * Ptil (lg p.1 + lg p.2 - GoodSeq.c lam) (lg p.2 - lg p.1) T H

/-- `D = min(1, e^{−2(Λ − 2 log(T'/2π))})`. -/
noncomputable def Dfac (Λ T' : ℝ) : ℝ := min 1 (Real.exp (-(2 * (Λ - 2 * ellT T'))))

lemma Dfac_nonneg (Λ T' : ℝ) : 0 ≤ Dfac Λ T' := le_min zero_le_one (Real.exp_pos _).le

noncomputable def KW : ℝ := max 2 (Real.exp (2 ^ 2) / (2 * Real.sqrt Real.pi))

lemma KW_pos : 0 < KW := lt_max_of_lt_left (by norm_num)

lemma WV_le_D (Λ T' : ℝ) : WV Λ T' ≤ KW * Dfac Λ T' := by
  unfold WV Dfac
  have h1 := V_le_two (Λ - 2 * ellT T')
  have h2 := V_le_exp_k (k := 2) (by norm_num) (Λ - 2 * ellT T')
  rcases le_total 1 (Real.exp (-(2 * (Λ - 2 * ellT T')))) with h | h
  · rw [min_eq_left h, mul_one]; exact h1.trans (le_max_left _ _)
  · rw [min_eq_right h]
    refine h2.trans ?_
    gcongr; exact le_max_right _ _

noncomputable def c16 : ℝ := Real.exp (6 ^ 2) / (6 * Real.sqrt Real.pi) * Real.exp (12 * ellT 16)

lemma c16_pos : 0 < c16 := by
  unfold c16; have := Real.sqrt_pos.mpr Real.pi_pos; positivity

lemma WV16_le (Λ : ℝ) : WV Λ 16 ≤ c16 * Real.exp (-(6 * Λ)) := by
  unfold WV c16
  refine (V_le_exp_k (k := 6) (by norm_num) _).trans (le_of_eq ?_)
  rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- `Dfac (Λ − c) T' = Dfac Λ (T' e^{c/2})`. -/
lemma Dfac_shift (Λ c : ℝ) {T' : ℝ} (hT : 0 < T') :
    Dfac (Λ - c) T' = Dfac Λ (T' * Real.exp (c / 2)) := by
  unfold Dfac ellT
  rw [show T' * Real.exp (c / 2) / (2 * Real.pi) = T' / (2 * Real.pi) * Real.exp (c / 2) by ring,
    Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
  congr 3; ring

/-- **Pair bound** (generic, with the shift `c`). -/
theorem norm_zz_le {T H : ℝ} (hT : 16 ≤ T) (hH : 0 < H) {m n : ℕ} (hmn : m < n) :
    ‖zz lam T H (m, n)‖ ≤ Real.exp (6 * GoodSeq.c lam) * (|lam (m + 1)| * |lam (n + 1)| * Real.exp (-((lg m + lg n) / 2)) *
      (c16 * Real.exp (-(6 * (lg m + lg n))) * (((n : ℝ) + 1) / ((n : ℝ) - m)) +
        (((n : ℝ) + 1) / ((n : ℝ) - m)) ^ 2 *
          (7 * Kphi * Real.exp (-((lg m + lg n) / 2)) * Dfac (lg m + lg n) ((T + H) * Real.exp (GoodSeq.c lam / 2)) +
            3 * KW * Dfac (lg m + lg n) ((T + H) * Real.exp (GoodSeq.c lam / 2)) / H))) := by
  have hne : m ≠ n := hmn.ne
  unfold zz
  simp only [hne, if_false]
  set c := GoodSeq.c lam with hcdef
  have hc : 0 ≤ c := GoodSeq.hc
  set Λ := lg m + lg n with hΛ
  set T'' := (T + H) * Real.exp (c / 2) with hT''
  set lam' := lg n - lg m with hlam
  have hlam0 : lam' ≠ 0 := by
    have : lg m < lg n := by
      unfold lg; exact Real.log_lt_log (by positivity) (by exact_mod_cast (by omega : m + 1 < n + 1))
    rw [hlam]; linarith
  have hinv := inv_abs_lg_sub_le hmn
  have hlpos : 0 < |lam'| := abs_pos.mpr hlam0
  have hTH : 0 < T + H := by linarith
  have hDs : Dfac (Λ - c) (T + H) = Dfac Λ T'' := Dfac_shift Λ c hTH
  have hec : Real.exp (c / 2) ≤ Real.exp (6 * c) := Real.exp_le_exp.mpr (by linarith)
  have he1 : 1 ≤ Real.exp (6 * c) := Real.one_le_exp (by linarith)
  have hΦ : ∀ t ∈ Icc 16 (T + H), phiD (Λ - c) t ≤
      Kphi * Real.exp (6 * c) * Real.exp (-(Λ / 2)) * Dfac Λ T'' := by
    intro t ht
    refine (phiD_le_min (Λ - c) (by linarith [ht.1]) ht.2).trans ?_
    rw [show min 1 (Real.exp (-(2 * (Λ - c - 2 * ellT (T + H))))) = Dfac Λ T'' from hDs]
    have e : Real.exp (-((Λ - c) / 2)) = Real.exp (c / 2) * Real.exp (-(Λ / 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e]
    have := Kphi_pos
    have := Dfac_nonneg Λ T''
    have : Kphi * (Real.exp (c / 2) * Real.exp (-(Λ / 2))) ≤ Kphi * (Real.exp (6 * c) * Real.exp (-(Λ / 2))) := by
      gcongr
    calc Kphi * (Real.exp (c / 2) * Real.exp (-(Λ / 2))) * Dfac Λ T''
        ≤ Kphi * (Real.exp (6 * c) * Real.exp (-(Λ / 2))) * Dfac Λ T'' := by gcongr
      _ = _ := by ring
  have hP := norm_Ptil_le (Λ := Λ - c) (lam := lam') hT hH hlam0 hΦ
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  unfold coefG
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  simp only
  rw [← hΛ]
  have hq : 1 / |lam'| ≤ ((n : ℝ) + 1) / ((n : ℝ) - m) := hinv
  have hq0 : 0 ≤ ((n : ℝ) + 1) / ((n : ℝ) - m) := by
    have : (m : ℝ) < n := by exact_mod_cast hmn
    have : (0 : ℝ) < (n : ℝ) - m := by linarith
    positivity
  have hq2 : 1 / lam' ^ 2 ≤ (((n : ℝ) + 1) / ((n : ℝ) - m)) ^ 2 := by
    rw [← sq_abs, one_div, ← inv_pow, ← one_div]
    exact pow_le_pow_left₀ (by positivity) hq 2
  have hW16 : WV (Λ - c) 16 ≤ Real.exp (6 * c) * (c16 * Real.exp (-(6 * Λ))) := by
    refine (WV16_le (Λ - c)).trans (le_of_eq ?_)
    rw [show -(6 * (Λ - c)) = 6 * c + -(6 * Λ) by ring, Real.exp_add]; ring
  have hWT : WV (Λ - c) (T + H) ≤ KW * Dfac Λ T'' := hDs ▸ WV_le_D (Λ - c) (T + H)
  have hW16' : 0 ≤ WV (Λ - c) 16 := V_nonneg _
  have hD := Dfac_nonneg Λ T''
  have hK := Kphi_pos
  have hKW := KW_pos
  have hpos : 0 ≤ |lam (m + 1)| * |lam (n + 1)| * Real.exp (-(Λ / 2)) := by positivity
  rw [show -((lg m + lg n) / 2) = -(Λ / 2) by rw [hΛ]]
  set q := ((n : ℝ) + 1) / ((n : ℝ) - m) with hqdef
  set Φ := Kphi * Real.exp (6 * c) * Real.exp (-(Λ / 2)) * Dfac Λ T'' with hΦdef
  have hPb : WV (Λ - c) 16 / |lam'| + (7 * Φ + 3 * WV (Λ - c) (T + H) / H) / lam' ^ 2 ≤
      Real.exp (6 * c) * (c16 * Real.exp (-(6 * Λ)) * q +
        q ^ 2 * (7 * Kphi * Real.exp (-(Λ / 2)) * Dfac Λ T'' + 3 * KW * Dfac Λ T'' / H)) := by
    have t1 : WV (Λ - c) 16 / |lam'| ≤ Real.exp (6 * c) * (c16 * Real.exp (-(6 * Λ))) * q := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul hW16 hq (by positivity) (by have := c16_pos; positivity)
    have hB : 7 * Φ + 3 * WV (Λ - c) (T + H) / H ≤
        Real.exp (6 * c) * (7 * Kphi * Real.exp (-(Λ / 2)) * Dfac Λ T'' + 3 * KW * Dfac Λ T'' / H) := by
      have h3 : 3 * WV (Λ - c) (T + H) / H ≤ 3 * (KW * Dfac Λ T'') / H := by gcongr
      have h4 : 3 * (KW * Dfac Λ T'') / H ≤ Real.exp (6 * c) * (3 * KW * Dfac Λ T'' / H) := by
        have h0 : 0 ≤ 3 * KW * Dfac Λ T'' / H := by positivity
        have := mul_le_mul_of_nonneg_right he1 h0
        linarith [show 3 * (KW * Dfac Λ T'') / H = 3 * KW * Dfac Λ T'' / H by ring]
      rw [hΦdef]
      nlinarith
    have hB0 : 0 ≤ 7 * Φ + 3 * WV (Λ - c) (T + H) / H := by
      have := V_nonneg (Λ - c - 2 * ellT (T + H)); unfold WV; positivity
    have t2 : (7 * Φ + 3 * WV (Λ - c) (T + H) / H) / lam' ^ 2 ≤
        Real.exp (6 * c) * (7 * Kphi * Real.exp (-(Λ / 2)) * Dfac Λ T'' + 3 * KW * Dfac Λ T'' / H) * q ^ 2 := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul hB hq2 (by positivity) (by positivity)
    nlinarith
  calc |lam (m + 1)| * |lam (n + 1)| * Real.exp (-(Λ / 2)) * ‖Ptil (Λ - c) lam' T H‖
      ≤ |lam (m + 1)| * |lam (n + 1)| * Real.exp (-(Λ / 2)) *
        (Real.exp (6 * c) * (c16 * Real.exp (-(6 * Λ)) * q +
          q ^ 2 * (7 * Kphi * Real.exp (-(Λ / 2)) * Dfac Λ T'' + 3 * KW * Dfac Λ T'' / H))) :=
        mul_le_mul_of_nonneg_left (hP.trans hPb) hpos
    _ = _ := by ring

end RamanujanTau.TwistedMoment
