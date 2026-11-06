/-
# The lag product `F(u)F(u')`, `F = Z·|M|²`, expanded; diagonal / off-diagonal split

For a real coefficient sequence `β` (Selberg's `βSel y`), on the line

    |M(6+iu)|² = Σ_{a,b ∈ [1,y]} wc(a,b) (b/a)^{iu},      wc(a,b) = β(a)β(b)(ab)^{−1/2}   (`wM_expand`)

and with `ShiftAFE.ZH_mul_ZH_afe`

    F(u)F(u') = 2 Re[ U(u,u') Σ_{a,b,c,d} wc(a,b)wc(c,d)(b/a)^{iu}(d/c)^{iu'} S(u,u') ],
    S(u,u') = Σ_{m,n} τ(m)τ(n) m^{−(6+iu)} n^{−(6−iu')} W̃_{u,u'}(4π²mn)              (`lag_product`).

With `u' = u+v` the `u`-frequency of the `(m,n,a,b,c,d)` term is `log(bdn/(acm))`; the
**diagonal** is `bdn = acm` (`isDiag`).  `diagS` is the diagonal part of `S` for a fixed
quadruple, `DiagLag` the full diagonal of `F(u)F(u+v)`; `OffLag = F(u)F(u+v) − DiagLag`
is the off-diagonal remainder (equal to `2Re[U Σ wc wc (…) (S − diagS)]`, `lag_split`).
Level 1.
-/
import RamanujanTau.SelbergKey.Lag
import RamanujanTau.HafnerMV2.Main

set_option autoImplicit false

namespace RamanujanTau.SelbergKey

open Complex MeasureTheory Set Filter RamanujanTau.HeckeL RamanujanTau.HeckeAFE
open scoped Real ComplexConjugate

/-- The coefficient `wc(a,b) = β(a)β(b)(ab)^{−1/2}` of `|M|²`. -/
noncomputable def wc (β : ℕ → ℝ) (a b : ℕ) : ℝ :=
  β a * β b * Real.exp (-((Real.log a + Real.log b) / 2))

/-- The phase `(b/a)^{iu}`. -/
noncomputable def eph (a b : ℕ) (u : ℝ) : ℂ := cexp (u * I * ((Real.log b - Real.log a : ℝ) : ℂ))

/-- **`|M(6+iu)|²` as a finite twisted sum.** -/
theorem wM_expand (β : ℕ → ℝ) (y : ℕ) (u : ℝ) :
    ((HafnerProportion.wM (fun n => (β n : ℂ)) y u : ℝ) : ℂ) =
      ∑ a ∈ Finset.Icc 1 y, ∑ b ∈ Finset.Icc 1 y, (wc β a b : ℂ) * eph a b u := by
  unfold HafnerProportion.wM
  set z := HafnerProportion.Mc (fun n => (β n : ℂ)) y (6 + u * I) with hz
  have h1 : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h1, hz]
  unfold HafnerProportion.Mc
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
  have ha1 := (Finset.mem_Icc.1 ha).1
  have hb1 := (Finset.mem_Icc.1 hb).1
  rw [HafnerMV2.cpow_line ha1, HafnerMV2.cpow_line hb1, map_mul, Complex.conj_ofReal,
    show ((Real.exp (-(Real.log b / 2)) : ℝ) : ℂ) * cexp (-((u * Real.log b : ℝ) : ℂ) * I) =
      ((Real.exp (-(Real.log b / 2)) : ℝ) : ℂ) * cexp (-((u * Real.log b : ℝ) : ℂ) * I) from rfl,
    HafnerMV2.conj_term]
  unfold wc eph
  have e1 : Real.exp (-((Real.log a + Real.log b) / 2)) =
      Real.exp (-(Real.log a / 2)) * Real.exp (-(Real.log b / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : cexp (u * I * ((Real.log b - Real.log a : ℝ) : ℂ)) =
      cexp (-((u * Real.log a : ℝ) : ℂ) * I) * cexp (((u * Real.log b : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [e1, e2]; push_cast; ring

/-- The normalized term of the lag series `S(u,u')`. -/
noncomputable def sTerm (u u' : ℝ) (p : ℕ × ℕ) : ℂ :=
  tauC p.1 * tauC p.2 * (p.1 : ℂ) ^ (-(6 + u * I)) * (p.2 : ℂ) ^ (-(6 - u' * I)) *
    Wsh u u' (4 * π ^ 2 * p.1 * p.2)

/-- The lag series `S(u,u') = Σ_{m,n} sTerm`. -/
noncomputable def Sl (u u' : ℝ) : ℂ := ∑' p : ℕ × ℕ, sTerm u u' p

/-- The diagonal condition for the quadruple `(a,b,c,d)`: `b d n = a c m`. -/
def isDiag (a b c d : ℕ) (p : ℕ × ℕ) : Prop := p.2 * b * d = p.1 * a * c

instance (a b c d : ℕ) (p : ℕ × ℕ) : Decidable (isDiag a b c d p) := by
  unfold isDiag; infer_instance

/-- The diagonal part of `S` for the quadruple `(a,b,c,d)`. -/
noncomputable def diagS (a b c d : ℕ) (u u' : ℝ) : ℂ :=
  ∑' p : ℕ × ℕ, if isDiag a b c d p then sTerm u u' p else 0

/-- `F = Z·|M|²` for Selberg's real coefficients. -/
noncomputable def Fsel (β : ℕ → ℝ) (y : ℕ) (u : ℝ) : ℝ :=
  HafnerProportion.ZH u * HafnerProportion.wM (fun n => (β n : ℂ)) y u

/-- The quadruple sum `Σ_{a,b,c,d} wc wc (b/a)^{iu}(d/c)^{iu'} G(a,b,c,d)`. -/
noncomputable def quadSum (β : ℕ → ℝ) (y : ℕ) (u u' : ℝ) (G : ℕ → ℕ → ℕ → ℕ → ℂ) : ℂ :=
  ∑ a ∈ Finset.Icc 1 y, ∑ b ∈ Finset.Icc 1 y, ∑ c ∈ Finset.Icc 1 y, ∑ d ∈ Finset.Icc 1 y,
    (wc β a b : ℂ) * eph a b u * ((wc β c d : ℂ) * eph c d u') * G a b c d

/-- **The lag product, expanded.** -/
theorem lag_product (β : ℕ → ℝ) (y : ℕ) (u u' : ℝ) :
    Fsel β y u * Fsel β y u' =
      2 * (Ush u u' * quadSum β y u u' (fun _ _ _ _ => Sl u u')).re := by
  unfold Fsel
  have hZ := ZH_mul_ZH_afe u u'
  set W1 := HafnerProportion.wM (fun n => (β n : ℂ)) y u
  set W2 := HafnerProportion.wM (fun n => (β n : ℂ)) y u'
  have hq : quadSum β y u u' (fun _ _ _ _ => Sl u u') = ((W1 * W2 : ℝ) : ℂ) * Sl u u' := by
    unfold quadSum
    rw [Complex.ofReal_mul, wM_expand, wM_expand, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [hq]
  have : Ush u u' * (((W1 * W2 : ℝ) : ℂ) * Sl u u') = ((W1 * W2 : ℝ) : ℂ) * (Ush u u' * Sl u u') := by
    ring
  rw [this, Complex.re_ofReal_mul]
  have hS : Sl u u' = ∑' p : ℕ × ℕ, tauC p.1 * tauC p.2 * (p.1 : ℂ) ^ (-(6 + u * I)) *
      (p.2 : ℂ) ^ (-(6 - u' * I)) * Wsh u u' (4 * π ^ 2 * p.1 * p.2) := rfl
  rw [hS]
  calc HafnerProportion.ZH u * W1 * (HafnerProportion.ZH u' * W2)
      = (HafnerProportion.ZH u * HafnerProportion.ZH u') * (W1 * W2) := by ring
    _ = _ := by rw [hZ]; ring

/-- The **diagonal** of the lag product `F(u)F(u+v)`. -/
noncomputable def DiagLag (β : ℕ → ℝ) (y : ℕ) (u v : ℝ) : ℝ :=
  2 * (Ush u (u + v) * quadSum β y u (u + v) (fun a b c d => diagS a b c d u (u + v))).re

/-- The **off-diagonal** remainder `F(u)F(u+v) − DiagLag`. -/
noncomputable def OffLag (β : ℕ → ℝ) (y : ℕ) (u v : ℝ) : ℝ :=
  Fsel β y u * Fsel β y (u + v) - DiagLag β y u v

/-- **The split**: `OffLag = 2 Re[U Σ wc wc (…)(S − diagS)]`, i.e. exactly the terms of the exact
expansion with `bdn ≠ acm` (given absolute convergence of `S`, `S − diagS` is the off-diagonal
sub-sum). -/
theorem lag_split (β : ℕ → ℝ) (y : ℕ) (u v : ℝ) :
    OffLag β y u v = 2 * (Ush u (u + v) *
      quadSum β y u (u + v) (fun a b c d => Sl u (u + v) - diagS a b c d u (u + v))).re := by
  unfold OffLag DiagLag
  rw [lag_product]
  have hlin : quadSum β y u (u + v) (fun a b c d => Sl u (u + v) - diagS a b c d u (u + v)) =
      quadSum β y u (u + v) (fun _ _ _ _ => Sl u (u + v)) -
        quadSum β y u (u + v) (fun a b c d => diagS a b c d u (u + v)) := by
    unfold quadSum
    simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hlin, mul_sub, Complex.sub_re]
  ring

/-! ## Absolute convergence of the lag series -/

/-- `|W(a,b;ξ)| ≪ ξ^{−2}` on `Re a = Re b = 6` (line `Re z = 2`). -/
lemma norm_W2sh_le {a b : ℂ} (ha : a.re = 6) (hb : b.re = 6) {ξ : ℝ} (hξ : 0 < ξ) :
    ‖W2sh a b ξ 2‖ ≤ (2 * π)⁻¹ * (Real.Gamma 8 * Real.Gamma 8 * (Real.exp (2 ^ 2) * 2⁻¹) *
      ∫ y : ℝ, Real.exp (-1 * y ^ 2)) * ξ ^ (-(2 : ℝ)) := by
  unfold W2sh vline
  rw [norm_mul, norm_inv, show ‖(2 * π : ℂ)‖ = 2 * π by
    rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]]
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h1 : (0:ℝ) < a.re + 2 := by rw [ha]; norm_num
  have h2 : (0:ℝ) < b.re + 2 := by rw [hb]; norm_num
  set K : ℝ := Real.Gamma 8 * Real.Gamma 8 * ξ ^ (-(2:ℝ)) * (Real.exp (2 ^ 2) * 2⁻¹)
  have hbd : ∀ y : ℝ, ‖Gamma (a + (((2:ℝ) : ℂ) + y * I)) * Gamma (b + (((2:ℝ) : ℂ) + y * I)) *
        (ξ : ℂ) ^ (-(((2:ℝ) : ℂ) + y * I)) * cexp ((((2:ℝ) : ℂ) + y * I) ^ 2) /
          (((2:ℝ) : ℂ) + y * I)‖ ≤ K * Real.exp (-1 * y ^ 2) := by
    intro y
    have := norm_W2sh_integrand_le (a := a) (b := b) (c := 2) (by norm_num) h1 h2 hξ y
    rw [ha, hb, show (6:ℝ) + 2 = 8 by norm_num] at this
    exact this
  refine (norm_integral_le_of_norm_le ((integrable_exp_neg_mul_sq one_pos).const_mul K)
    (Eventually.of_forall hbd)).trans (le_of_eq ?_)
  rw [integral_const_mul]
  simp only [K]
  ring

/-- **The lag series converges absolutely.** -/
theorem summable_sTerm (u u' : ℝ) : Summable (sTerm u u') := by
  set C0 : ℝ := (2 * π)⁻¹ * (Real.Gamma 8 * Real.Gamma 8 * (Real.exp (2 ^ 2) * 2⁻¹) *
      ∫ y : ℝ, Real.exp (-1 * y ^ 2))
  have hC0 : 0 ≤ C0 := by
    have : 0 ≤ ∫ y : ℝ, Real.exp (-1 * y ^ 2) := integral_nonneg fun _ => (Real.exp_pos _).le
    have := Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 8)
    positivity
  set G : ℝ := ‖Gamma (6 + u * I) * Gamma (6 - u' * I)‖
  have hG : 0 < G := norm_pos_iff.mpr (mul_ne_zero (HafnerProportion.Gamma_line_ne_zero u)
    (Gamma_six_sub_ne u'))
  set g : ℕ → ℝ := fun m => |(tau m : ℝ)| / (m : ℝ) ^ (8 : ℝ)
  have hg : Summable g := RamanujanTau.HeckeConvex.summable_abs_tau_div_rpow (by norm_num)
  have hg0 : ∀ m, 0 ≤ g m := fun m => by simp only [g]; positivity
  refine Summable.of_norm_bounded (g := fun p : ℕ × ℕ =>
    (C0 / G * (4 * π ^ 2) ^ (-(2:ℝ))) * (g p.1 * g p.2))
    ((Summable.mul_of_nonneg hg hg hg0 hg0).mul_left _) fun p => ?_
  obtain ⟨m, n⟩ := p
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [sTerm, tauC_zero, g]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [sTerm, tauC_zero, g]
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have hξ : (0:ℝ) < 4 * π ^ 2 * m * n := by positivity
  have hW : ‖Wsh u u' (4 * π ^ 2 * m * n)‖ ≤ C0 * (4 * π ^ 2 * m * n) ^ (-(2:ℝ)) / G := by
    unfold Wsh
    rw [norm_div]
    exact div_le_div_of_nonneg_right (norm_W2sh_le (by simp) (by simp) hξ) hG.le
  have hτm : ‖tauC m‖ = |(tau m : ℝ)| := by simp [tauC, Complex.norm_intCast]
  have hτn : ‖tauC n‖ = |(tau n : ℝ)| := by simp [tauC, Complex.norm_intCast]
  unfold sTerm
  simp only
  rw [norm_mul, norm_mul, norm_mul, norm_mul, hτm, hτn, norm_natCast_cpow_of_pos hm,
    norm_natCast_cpow_of_pos hn]
  have e1 : (-(6 + (u : ℂ) * I)).re = -6 := by simp
  have e2 : (-(6 - (u' : ℂ) * I)).re = -6 := by simp
  rw [e1, e2]
  have hsplit : (4 * π ^ 2 * m * n : ℝ) ^ (-(2:ℝ)) =
      (4 * π ^ 2) ^ (-(2:ℝ)) * ((m : ℝ) ^ (-(2:ℝ)) * (n : ℝ) ^ (-(2:ℝ))) := by
    rw [mul_assoc, Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow hmr.le hnr.le]
  have hm8 : (m : ℝ) ^ (-6:ℝ) * (m : ℝ) ^ (-(2:ℝ)) = 1 / (m : ℝ) ^ (8:ℝ) := by
    rw [← Real.rpow_add hmr, one_div, ← Real.rpow_neg hmr.le]; norm_num
  have hn8 : (n : ℝ) ^ (-6:ℝ) * (n : ℝ) ^ (-(2:ℝ)) = 1 / (n : ℝ) ^ (8:ℝ) := by
    rw [← Real.rpow_add hnr, one_div, ← Real.rpow_neg hnr.le]; norm_num
  have h0 : 0 ≤ |(tau m : ℝ)| * |(tau n : ℝ)| * (m : ℝ) ^ (-6:ℝ) * (n : ℝ) ^ (-6:ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (Real.rpow_nonneg hmr.le _)) (Real.rpow_nonneg hnr.le _)
  calc |(tau m : ℝ)| * |(tau n : ℝ)| * (m : ℝ) ^ (-6:ℝ) * (n : ℝ) ^ (-6:ℝ) *
        ‖Wsh u u' (4 * π ^ 2 * m * n)‖
      ≤ |(tau m : ℝ)| * |(tau n : ℝ)| * (m : ℝ) ^ (-6:ℝ) * (n : ℝ) ^ (-6:ℝ) *
        (C0 * (4 * π ^ 2 * m * n) ^ (-(2:ℝ)) / G) := mul_le_mul_of_nonneg_left hW h0
    _ = (C0 / G * (4 * π ^ 2) ^ (-(2:ℝ))) *
        (|(tau m : ℝ)| * ((m : ℝ) ^ (-6:ℝ) * (m : ℝ) ^ (-(2:ℝ))) *
          (|(tau n : ℝ)| * ((n : ℝ) ^ (-6:ℝ) * (n : ℝ) ^ (-(2:ℝ))))) := by
        rw [hsplit]; ring
    _ = _ := by rw [hm8, hn8]; simp only [g]; ring

/-- Consequently the diagonal / off-diagonal split of `S` is a split of absolutely convergent
sums: `S − diagS = Σ_{bdn ≠ acm} sTerm`. -/
theorem Sl_sub_diagS (a b c d : ℕ) (u u' : ℝ) :
    Sl u u' - diagS a b c d u u' =
      ∑' p : ℕ × ℕ, if isDiag a b c d p then 0 else sTerm u u' p := by
  have hs := summable_sTerm u u'
  have h1 : Summable fun p => if isDiag a b c d p then sTerm u u' p else 0 :=
    hs.indicator {p | isDiag a b c d p} |>.congr fun p => by
      simp [Set.indicator, Set.mem_setOf_eq]
  have h2 : Summable fun p => if isDiag a b c d p then 0 else sTerm u u' p :=
    hs.indicator {p | ¬ isDiag a b c d p} |>.congr fun p => by
      by_cases hp : isDiag a b c d p <;> simp [Set.indicator, hp]
  unfold Sl diagS
  rw [sub_eq_iff_eq_add, ← h2.tsum_add h1]
  congr 1; ext p
  split_ifs <;> simp

end RamanujanTau.SelbergKey
