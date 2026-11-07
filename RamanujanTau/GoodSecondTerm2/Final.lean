/-
# Good's second-term asymptotic, unconditionally

Sandwich argument: `I(u) = ∫_0^u |L(Δ,6+it)|² dt` is monotone, so
`avg_{[T−H,T]} I ≤ I(T) ≤ avg_{[T,T+H]} I`, and the `u`-average of `Off` is
`Σ_p zz` (`avgOff_eq`), which is `O(T^{599/600})` (`avgOff_le`, via the SCS bound).
-/
import RamanujanTau.GoodSecondTerm2.Param

set_option autoImplicit false

namespace RamanujanTau.GoodSecondTerm2

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.ZetaAFE RamanujanTau.GoodSecondTerm RamanujanTau.SubconvexityCond RamanujanTau.HeckeL
open scoped Interval

/-- The main term. -/
noncomputable def mainF (u : ℝ) : ℝ :=
  2 * c0 * (u * Real.log (u / (2 * Real.pi))) + (2 * gammaD - 2 * c0) * u

/-- The mean square `I(u) = ∫_0^u |L(Δ, 6+it)|² dt`. -/
noncomputable def Ims (u : ℝ) : ℝ := ∫ t in (0 : ℝ)..u, zsqD t

lemma continuous_Ims : Continuous Ims := by
  unfold Ims
  exact intervalIntegral.continuous_primitive (fun a b => continuous_zsqD.intervalIntegrable a b) 0

lemma Ims_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : Ims a ≤ Ims b := by
  unfold Ims
  exact intervalIntegral.integral_mono_interval le_rfl ha hab
    (Eventually.of_forall fun t => by unfold zsqD; positivity)
    (continuous_zsqD.intervalIntegrable 0 b)

lemma hasDerivAt_mainF {x : ℝ} (hx : 0 < x) :
    HasDerivAt mainF (2 * c0 * (Real.log (x / (2 * Real.pi)) + 1) + (2 * gammaD - 2 * c0)) x := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have h1 : HasDerivAt (fun y : ℝ => y / (2 * Real.pi)) (1 / (2 * Real.pi)) x :=
    (hasDerivAt_id x).div_const _
  have h2 := h1.log (by positivity)
  have h3 := (hasDerivAt_id x).mul h2
  have h4 := ((h3.const_mul (2 * c0)).add ((hasDerivAt_id x).const_mul (2 * gammaD - 2 * c0)))
  unfold mainF
  convert h4 using 1
  simp only [id]
  field_simp

lemma continuousOn_OffInt {a b : ℝ} (ha : 16 ≤ a) (hab : a ≤ b) : ContinuousOn OffInt (Icc a b) := by
  have h16 : (0 : ℝ) < 16 := by norm_num
  have hcont : ∀ p, ContinuousOn (fun u => ∫ t in (16 : ℝ)..u, boD t p) (Icc a b) := by
    intro p u hu
    have hu0 : 0 < u := by linarith [hu.1]
    have hII : IntervalIntegrable (fun t => boD t p) volume 16 u :=
      ((continuousOn_boD' p).mono (by
        intro x hx; rw [uIcc_of_le (by linarith [hu.1])] at hx; exact lt_of_lt_of_le h16 hx.1)).intervalIntegrable
    exact (intervalIntegral.integral_hasDerivAt_right hII
      ((continuousOn_boD' p).stronglyMeasurableAtFilter isOpen_Ioi u hu0)
      ((continuousOn_boD' p).continuousAt (isOpen_Ioi.mem_nhds hu0))).continuousAt.continuousWithinAt
  have hb : ∀ p u, u ∈ Icc a b → ‖∫ t in (16 : ℝ)..u, boD t p‖ ≤ b * (2 * b ^ 2) * tt7 p := by
    intro p u hu
    have h16u : 16 ≤ u := by linarith [hu.1]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 2 * b ^ 2 * tt7 p) fun t ht => ?_).trans ?_
    · rw [uIoc_of_le h16u] at ht
      exact norm_boD_le h16 ⟨ht.1.le, ht.2.trans hu.2⟩ p
    · rw [abs_of_nonneg (by linarith)]
      have h7 : 0 ≤ tt7 p := by
        unfold tt7
        exact mul_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (by positivity) _))
          (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (by positivity) _))
      have : 0 ≤ 2 * b ^ 2 * tt7 p := mul_nonneg (by positivity) h7
      calc 2 * b ^ 2 * tt7 p * (u - 16) ≤ 2 * b ^ 2 * tt7 p * b :=
            mul_le_mul_of_nonneg_left (by linarith [hu.2]) this
        _ = _ := by ring
  unfold OffInt
  exact continuousOn_tsum hcont (summable_tt7.mul_left (b * (2 * b ^ 2))) hb

lemma continuousOn_mainF : ContinuousOn mainF (Ioi 0) := fun x hx =>
  (hasDerivAt_mainF hx).continuousAt.continuousWithinAt

/-- Lipschitz bound for the main term near `T`. -/
lemma mainF_lip {T u : ℝ} (hT : 16 ≤ T) (hu1 : T / 2 ≤ u) (hu2 : u ≤ 2 * T) :
    |mainF u - mainF T| ≤ (2 * |c0| * (Real.log (2 * T) + 1) + |2 * gammaD - 2 * c0|) * |u - T| := by
  have hpi := Real.pi_lt_four
  have hpi0 := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hs : Convex ℝ (Icc (T / 2) (2 * T)) := convex_Icc _ _
  have hd : ∀ x ∈ Icc (T / 2) (2 * T), HasDerivWithinAt mainF
      (2 * c0 * (Real.log (x / (2 * Real.pi)) + 1) + (2 * gammaD - 2 * c0)) (Icc (T / 2) (2 * T)) x :=
    fun x hx => (hasDerivAt_mainF (by linarith [hx.1])).hasDerivWithinAt
  have hb : ∀ x ∈ Icc (T / 2) (2 * T),
      ‖2 * c0 * (Real.log (x / (2 * Real.pi)) + 1) + (2 * gammaD - 2 * c0)‖ ≤
        2 * |c0| * (Real.log (2 * T) + 1) + |2 * gammaD - 2 * c0| := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hl0 : 0 ≤ Real.log (x / (2 * Real.pi)) :=
      Real.log_nonneg (by rw [le_div_iff₀ (by positivity)]; linarith [hx.1])
    have hl1 : Real.log (x / (2 * Real.pi)) ≤ Real.log (2 * T) :=
      Real.log_le_log (by positivity) ((div_le_self hx0.le (by linarith)).trans hx.2)
    rw [Real.norm_eq_abs]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ Real.log (x / (2 * Real.pi)) + 1),
      abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have : 0 ≤ |c0| := abs_nonneg _
    gcongr
  have hTs : T ∈ Icc (T / 2) (2 * T) := ⟨by linarith, by linarith⟩
  have := hs.norm_image_sub_le_of_norm_hasDerivWithin_le (x := T) (y := u) hd hb hTs ⟨hu1, hu2⟩
  simpa [Real.norm_eq_abs] using this

/-- Average of the main term over `[a, a+H]` vs `H · main(T)`. -/
lemma avg_main {T a H : ℝ} (hT : 16 ≤ T) (hH : 0 < H) (ha1 : T / 2 ≤ a) (ha2 : a + H ≤ 2 * T)
    (hd : ∀ u ∈ Icc a (a + H), |u - T| ≤ H) :
    |(∫ u in a..a + H, mainF u) - H * mainF T| ≤
      H * ((2 * |c0| * (Real.log (2 * T) + 1) + |2 * gammaD - 2 * c0|) * H) := by
  set L := 2 * |c0| * (Real.log (2 * T) + 1) + |2 * gammaD - 2 * c0|
  have hL : 0 ≤ L := by
    have : 0 ≤ Real.log (2 * T) := Real.log_nonneg (by linarith)
    positivity
  have hint : IntervalIntegrable mainF volume a (a + H) :=
    (continuousOn_mainF.mono (fun x hx => by
      rw [uIcc_of_le (by linarith)] at hx; show 0 < x; linarith [hx.1])).intervalIntegrable
  have e : (∫ u in a..a + H, mainF u) - H * mainF T = ∫ u in a..a + H, (mainF u - mainF T) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const, intervalIntegral.integral_const]
    simp [smul_eq_mul]
  rw [e]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := a + H)
    (f := fun u => mainF u - mainF T) (C := L * H) (fun u hu => by
      rw [uIoc_of_le (by linarith)] at hu
      have hu' : u ∈ Icc a (a + H) := ⟨hu.1.le, hu.2⟩
      rw [Real.norm_eq_abs]
      refine (mainF_lip hT (by linarith [hu.1]) (by linarith [hu.2])).trans ?_
      exact mul_le_mul_of_nonneg_left (hd u hu') hL)
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  rw [show a + H - a = H by ring, abs_of_pos hH]; ring

/-- **The averaged identity.** For `16 ≤ a ≤ T`, `H = T^{299/300}`:
`|∫_a^{a+H} I − ∫_a^{a+H} main| ≤ H · C T^{599/600}`. -/
lemma avg_I : ∃ C : ℝ, ∀ T a : ℝ, 2 ^ (300 : ℕ) ≤ T → 16 ≤ a → a ≤ T →
    |(∫ u in a..a + T ^ (299 / 300 : ℝ), Ims u) - ∫ u in a..a + T ^ (299 / 300 : ℝ), mainF u| ≤
      T ^ (299 / 300 : ℝ) * (C * T ^ (599 / 600 : ℝ)) := by
  obtain ⟨C₀, hC₀⟩ := avgOff_le
  obtain ⟨C₁, hC₁⟩ := good_reduction
  set C₁' := max C₁ 0
  refine ⟨C₀ + 2 * C₁', fun T a hT ha haT => ?_⟩
  have hav := hC₀ T a hT ha haT
  have hT1 : (1 : ℝ) ≤ T := (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)).trans hT
  clear hT
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le one_pos hT1
  set H : ℝ := T ^ (299 / 300 : ℝ) with hH
  have hH0 : 0 < H := by positivity
  have hHT : H ≤ T := by
    calc H ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
      _ = T := Real.rpow_one T
  have hOffI : IntervalIntegrable OffInt volume a (a + H) :=
    (continuousOn_OffInt ha (by linarith)).intervalIntegrable_of_Icc (by linarith)
  have hIc : IntervalIntegrable (fun u => (Ims u : ℂ)) volume a (a + H) :=
    (Complex.continuous_ofReal.comp continuous_Ims).intervalIntegrable _ _
  have hMc : IntervalIntegrable (fun u => (mainF u : ℂ)) volume a (a + H) := by
    refine (Complex.continuous_ofReal.comp_continuousOn (continuousOn_mainF.mono ?_)).intervalIntegrable
    intro x hx; rw [uIcc_of_le (by linarith)] at hx; show 0 < x; linarith [hx.1]
  set err : ℝ → ℂ := fun u => (Ims u : ℂ) - (mainF u : ℂ) - OffInt u with herr
  have hkey : (((∫ u in a..a + H, Ims u) - ∫ u in a..a + H, mainF u : ℝ) : ℂ) =
      (∫ u in a..a + H, OffInt u) + ∫ u in a..a + H, err u := by
    rw [herr, intervalIntegral.integral_sub (hIc.sub hMc) hOffI, intervalIntegral.integral_sub hIc hMc,
      intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
    push_cast; ring
  have hOffEq : (∫ u in a..a + H, OffInt u) = (H : ℂ) * ∑' p, zz a H p := by
    rw [← avgOff_eq ha hH0]
    have hH0' : (H : ℂ) ≠ 0 := by exact_mod_cast hH0.ne'
    field_simp
  have hOffN : ‖∫ u in a..a + H, OffInt u‖ ≤ H * (C₀ * T ^ (599 / 600 : ℝ)) := by
    rw [hOffEq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH0]
    exact mul_le_mul_of_nonneg_left hav hH0.le
  have h2T : (2 * T) ^ (9 / 10 : ℝ) ≤ 2 * T ^ (599 / 600 : ℝ) := by
    calc (2 * T) ^ (9 / 10 : ℝ) ≤ (2 * T) ^ (599 / 600 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = 2 ^ (599 / 600 : ℝ) * T ^ (599 / 600 : ℝ) := Real.mul_rpow (by norm_num) hT0.le
      _ ≤ 2 * T ^ (599 / 600 : ℝ) := by
          gcongr
          calc (2 : ℝ) ^ (599 / 600 : ℝ) ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
  have hErrN : ‖∫ u in a..a + H, err u‖ ≤ H * (2 * C₁' * T ^ (599 / 600 : ℝ)) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := a + H)
      (f := err) (C := C₁' * (2 * T) ^ (9 / 10 : ℝ)) (fun u hu => by
        rw [uIoc_of_le (by linarith)] at hu
        have h16u : 16 ≤ u := by linarith [hu.1]
        have hb := hC₁ u h16u
        have hu0 : 0 ≤ u := by linarith
        calc ‖err u‖ ≤ C₁ * u ^ (9 / 10 : ℝ) := hb
          _ ≤ C₁' * u ^ (9 / 10 : ℝ) := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
          _ ≤ C₁' * (2 * T) ^ (9 / 10 : ℝ) :=
              mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hu0 (by linarith [hu.2]) (by norm_num))
                (le_max_right _ _))
    refine this.trans ?_
    rw [show a + H - a = H by ring, abs_of_pos hH0]
    have hC1 : 0 ≤ C₁' := le_max_right _ _
    calc C₁' * (2 * T) ^ (9 / 10 : ℝ) * H ≤ C₁' * (2 * T ^ (599 / 600 : ℝ)) * H := by gcongr
      _ = _ := by ring
  have := congrArg norm hkey
  rw [Complex.norm_real, Real.norm_eq_abs] at this
  rw [this]
  refine (norm_add_le _ _).trans ?_
  linarith

lemma two_le_rpow300 {T : ℝ} (hT : 2 ^ (300 : ℕ) ≤ T) : 2 ≤ T ^ (1 / 300 : ℝ) := by
  have h := Real.rpow_le_rpow (by positivity) hT (by norm_num : (0:ℝ) ≤ 1 / 300)
  refine le_trans (le_of_eq ?_) h
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num

/-- `L(T) · H ≤ C T^{599/600}` for the Lipschitz constant of the main term. -/
lemma lipH_le {T : ℝ} (hT1 : 1 ≤ T) :
    (2 * |c0| * (Real.log (2 * T) + 1) + |2 * gammaD - 2 * c0|) * T ^ (299 / 300 : ℝ) ≤
      (2 * |c0| * (1200 + 1) + |2 * gammaD - 2 * c0|) * T ^ (599 / 600 : ℝ) := by
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le one_pos hT1
  have hlog : Real.log (2 * T) ≤ 1200 * T ^ (1 / 600 : ℝ) := by
    have := Real.log_le_rpow_div (x := 2 * T) (by linarith) (by norm_num : (0:ℝ) < 1 / 600)
    have h2 : (2 * T) ^ (1 / 600 : ℝ) ≤ 2 * T ^ (1 / 600 : ℝ) := by
      rw [Real.mul_rpow (by norm_num) hT0.le]
      gcongr
      calc (2 : ℝ) ^ (1 / 600 : ℝ) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    calc Real.log (2 * T) ≤ (2 * T) ^ (1 / 600 : ℝ) / (1 / 600) := this
      _ = 600 * (2 * T) ^ (1 / 600 : ℝ) := by ring
      _ ≤ 600 * (2 * T ^ (1 / 600 : ℝ)) := by gcongr
      _ = _ := by ring
  have hHp : T ^ (299 / 300 : ℝ) * T ^ (1 / 600 : ℝ) = T ^ (599 / 600 : ℝ) := by
    rw [← Real.rpow_add hT0]; norm_num
  have hHle : T ^ (299 / 300 : ℝ) ≤ T ^ (599 / 600 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
  have hH0 : 0 ≤ T ^ (299 / 300 : ℝ) := by positivity
  have hc : 0 ≤ |c0| := abs_nonneg _
  have hg : 0 ≤ |2 * gammaD - 2 * c0| := abs_nonneg _
  have h1 : Real.log (2 * T) * T ^ (299 / 300 : ℝ) ≤ 1200 * T ^ (599 / 600 : ℝ) := by
    rw [← hHp]
    calc Real.log (2 * T) * T ^ (299 / 300 : ℝ) ≤ 1200 * T ^ (1 / 600 : ℝ) * T ^ (299 / 300 : ℝ) :=
          mul_le_mul_of_nonneg_right hlog hH0
      _ = _ := by ring
  have e : (2 * |c0| * (Real.log (2 * T) + 1) + |2 * gammaD - 2 * c0|) * T ^ (299 / 300 : ℝ) =
      2 * |c0| * (Real.log (2 * T) * T ^ (299 / 300 : ℝ)) + 2 * |c0| * T ^ (299 / 300 : ℝ) +
        |2 * gammaD - 2 * c0| * T ^ (299 / 300 : ℝ) := by ring
  rw [e]
  have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 2 * |c0|)
  have := mul_le_mul_of_nonneg_left hHle (by positivity : (0:ℝ) ≤ 2 * |c0|)
  have := mul_le_mul_of_nonneg_left hHle hg
  nlinarith

/-- **Good's asymptotic for large `T`** (`T ≥ 2^{300}`), error `O(T^{599/600})`. -/
theorem good_second_term_large : ∃ C : ℝ, ∀ T : ℝ, 2 ^ (300 : ℕ) ≤ T →
    |Ims T - mainF T| ≤ C * T ^ (599 / 600 : ℝ) := by
  obtain ⟨C, hC⟩ := avg_I
  set Lc : ℝ := 2 * |c0| * (1200 + 1) + |2 * gammaD - 2 * c0|
  refine ⟨C + Lc, fun T hT => ?_⟩
  have h2 := two_le_rpow300 hT
  have hT1 : (1 : ℝ) ≤ T := (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)).trans hT
  have hT32 : (32 : ℝ) ≤ T := le_trans (by
    calc (32 : ℝ) = 2 ^ (5 : ℕ) := by norm_num
      _ ≤ 2 ^ (300 : ℕ) := pow_le_pow_right₀ (by norm_num) (by norm_num)) hT
  have hup' := hC T T hT
  have hlo' := hC T (T - T ^ (299 / 300 : ℝ)) hT
  clear hT
  have hT0 : (0 : ℝ) < T := by linarith
  set H : ℝ := T ^ (299 / 300 : ℝ) with hH
  have hH0 : 0 < H := by positivity
  have hHT2 : 2 * H ≤ T := by
    have : H * T ^ (1 / 300 : ℝ) = T := by
      rw [hH, ← Real.rpow_add hT0]; norm_num
    nlinarith
  have hup := hup' (by linarith) le_rfl
  have hlo := hlo' (by linarith) (by linarith)
  set L := 2 * |c0| * (Real.log (2 * T) + 1) + |2 * gammaD - 2 * c0|
  have hLH : L * H ≤ Lc * T ^ (599 / 600 : ℝ) := lipH_le hT1
  have hmu := avg_main (T := T) (a := T) (H := H) (by linarith) hH0 (by linarith) (by linarith)
    (fun u hu => by rw [abs_of_nonneg (by linarith [hu.1])]; linarith [hu.2])
  have hml := avg_main (T := T) (a := T - H) (H := H) (by linarith) hH0 (by linarith) (by linarith)
    (fun u hu => by rw [abs_of_nonpos (by linarith [hu.2])]; linarith [hu.1])
  -- monotonicity sandwich
  have hIu : H * Ims T ≤ ∫ u in T..T + H, Ims u := by
    have := intervalIntegral.integral_mono_on (a := T) (b := T + H) (f := fun _ => Ims T) (g := Ims)
      (by linarith) ((continuous_const (y := Ims T)).intervalIntegrable (μ := volume) _ _)
      (continuous_Ims.intervalIntegrable T (T + H)) (fun u hu => Ims_mono (by linarith) hu.1)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    calc H * Ims T = (T + H - T) * Ims T := by ring
      _ ≤ _ := this
  have hIl : (∫ u in T - H..T - H + H, Ims u) ≤ H * Ims T := by
    have := intervalIntegral.integral_mono_on (a := T - H) (b := T - H + H) (f := Ims) (g := fun _ => Ims T)
      (by linarith) (continuous_Ims.intervalIntegrable _ _)
      ((continuous_const (y := Ims T)).intervalIntegrable (μ := volume) _ _)
      (fun u hu => Ims_mono (by linarith [hu.1]) (by linarith [hu.2]))
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    calc _ ≤ _ := this
      _ = H * Ims T := by ring
  rw [abs_le] at hup hlo hmu hml ⊢
  have hA : H * (Ims T - mainF T) ≤ H * ((C + Lc) * T ^ (599 / 600 : ℝ)) := by nlinarith
  have hB : H * (-((C + Lc) * T ^ (599 / 600 : ℝ))) ≤ H * (Ims T - mainF T) := by nlinarith
  exact ⟨le_of_mul_le_mul_left hB hH0, le_of_mul_le_mul_left hA hH0⟩

/-- `|I(T) − main(T)| ≤ C T^{599/600}` for all `T ≥ 16`. -/
theorem Ims_sub_mainF_le : ∃ C : ℝ, ∀ T : ℝ, 16 ≤ T → |Ims T - mainF T| ≤ C * T ^ (599 / 600 : ℝ) := by
  obtain ⟨C₁, hC₁⟩ := good_second_term_large
  have hcont : ContinuousOn (fun T => Ims T - mainF T) (Icc 16 (2 ^ (300 : ℕ))) :=
    continuous_Ims.continuousOn.sub (continuousOn_mainF.mono fun x hx => by
      show 0 < x; linarith [hx.1])
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C₁ 0 + max C₂ 0, fun T hT => ?_⟩
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hp : 1 ≤ T ^ (599 / 600 : ℝ) := Real.one_le_rpow hT1 (by norm_num)
  have e1 : 0 ≤ max C₁ 0 := le_max_right _ _
  have e2 : 0 ≤ max C₂ 0 := le_max_right _ _
  by_cases hT' : 2 ^ (300 : ℕ) ≤ T
  · have := hC₁ T hT'
    have : C₁ * T ^ (599 / 600 : ℝ) ≤ max C₁ 0 * T ^ (599 / 600 : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
    nlinarith
  · have h := hC₂ T ⟨hT, (not_le.mp hT').le⟩
    rw [Real.norm_eq_abs] at h
    have : C₂ ≤ max C₂ 0 * T ^ (599 / 600 : ℝ) := by nlinarith [le_max_left C₂ 0]
    nlinarith

/-- **`OffDiagHyp (1/600)` holds unconditionally** (via the SCS bound `ShiftedConvolutionBound (1/21) (1/21)`). -/
theorem offDiagHyp_unconditional : OffDiagHyp (1 / 600) := by
  obtain ⟨C₁, hC₁⟩ := good_reduction
  obtain ⟨C₂, hC₂⟩ := Ims_sub_mainF_le
  refine ⟨max C₁ 0 + C₂, fun T hT => ?_⟩
  have h1 := hC₁ T hT
  have h2 := hC₂ T hT
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hp : T ^ (9 / 10 : ℝ) ≤ T ^ (599 / 600 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
  have h9 : 0 ≤ T ^ (9 / 10 : ℝ) := Real.rpow_nonneg hT0 _
  have e : (1 : ℝ) - 1 / 600 = 599 / 600 := by norm_num
  rw [e]
  have hOff : OffInt T = ((Ims T - mainF T : ℝ) : ℂ) -
      ((((∫ t in (0:ℝ)..T, ‖tauL (6 + t * I)‖ ^ 2) : ℝ) : ℂ) -
        ((2 * c0 * (T * Real.log (T / (2 * Real.pi))) + (2 * gammaD - 2 * c0) * T : ℝ) : ℂ) - OffInt T) := by
    unfold Ims zsqD mainF; push_cast; ring
  rw [hOff]
  refine (norm_sub_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  have : C₁ * T ^ (9 / 10 : ℝ) ≤ max C₁ 0 * T ^ (599 / 600 : ℝ) :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) h9).trans
      (mul_le_mul_of_nonneg_left hp (le_max_right _ _))
  nlinarith

/-- **Good's mean-square theorem with second term, unconditional.**
`∫_0^T |L(Δ, 6+it)|² dt = 2c₀ T log(T/2π) + (2γ_D − 2c₀) T + O(T^{599/600})`. -/
theorem good_second_term : ∃ C : ℝ, ∀ T : ℝ, 16 ≤ T →
    |(∫ t in (0:ℝ)..T, ‖tauL (6 + t * I)‖ ^ 2) -
      (2 * c0 * (T * Real.log (T / (2 * Real.pi))) + (2 * gammaD - 2 * c0) * T)| ≤
      C * T ^ (599 / 600 : ℝ) := by
  obtain ⟨C, hC⟩ := Ims_sub_mainF_le
  exact ⟨C, fun T hT => hC T hT⟩

end RamanujanTau.GoodSecondTerm2
