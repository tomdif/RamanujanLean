/-
# M3 step 6d: the pointwise diagonal evaluation

`diag_pointwise`: for `y ≥ 1`, `u ≥ 40`, `0 < |v| ≤ 1`, `16π²y⁴ ≤ u²`,

    |DiagLag(u,v) − 2 Re 𝒜(v, log(u/2π))| ≤ C (|v|·|𝒮(v)| + y^N u^{−1/10}).

Level 1.
-/
import RamanujanTau.SelbergKeyDiag2.Final3

set_option autoImplicit false

namespace RamanujanTau.SelbergKeyDiag2

open Complex Finset RamanujanTau.HafnerBridge RamanujanTau.HafnerBridge2 RamanujanTau.SelbergKey
  RamanujanTau.HeckeAFE
open RamanujanTau.GoodSecondTerm (c0 gammaD)
open scoped Real

lemma TT_ge {u v : ℝ} (hu : 2 ≤ u) (hv : |v| ≤ 1) : u ^ 2 / 4 ≤ TT u v := by
  unfold TT
  have h1 := Tq_ge u
  have h2 := Tq_ge (u + v)
  have h3 : u / 2 ≤ Tq u := le_trans (by rw [abs_of_pos (by linarith)]; linarith) h1
  have h5 : u - 1 ≤ |u + v| := by
    rw [abs_of_pos (by linarith [(abs_le.1 hv).1])]; linarith [(abs_le.1 hv).1]
  have h4 : u / 2 ≤ Tq (u + v) := le_trans (by linarith) h2
  calc u ^ 2 / 4 = (u / 2) * (u / 2) := by ring
    _ ≤ Tq u * Tq (u + v) := mul_le_mul h3 h4 (by linarith) (by linarith [Tq_pos u])

lemma rpow20_le {Y u r : ℝ} (hY : 1 ≤ Y) (hu : 0 < u) (hr0 : 0 ≤ r) (hr : r ≤ 16 * π ^ 2 * Y ^ 4 / u ^ 2) :
    r ^ (1 / 20 : ℝ) ≤ 2 * Y * u ^ (-(1 / 10 : ℝ)) := by
  have hY0 : 0 < Y := by linarith
  refine (Real.rpow_le_rpow hr0 hr (by norm_num)).trans ?_
  rw [Real.div_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)]
  have h1 : (16 * π ^ 2) ^ (1 / 20 : ℝ) ≤ 2 := by
    have h16 : 16 * π ^ 2 ≤ (2:ℝ) ^ (20:ℕ) := by
      have := Real.pi_lt_four; nlinarith [Real.pi_pos]
    have := Real.rpow_le_rpow (by positivity) h16 (by norm_num : (0:ℝ) ≤ 1 / 20)
    refine this.trans (le_of_eq ?_)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have h2 : (Y ^ 4) ^ (1 / 20 : ℝ) ≤ Y := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hY0.le]
    calc Y ^ ((4:ℕ) * (1 / 20 : ℝ)) ≤ Y ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hY (by norm_num)
      _ = Y := Real.rpow_one Y
  have h3 : (u ^ 2) ^ (1 / 20 : ℝ) = u ^ (1 / 10 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]; norm_num
  rw [h3, Real.rpow_neg hu.le, div_eq_mul_inv]
  have : 0 ≤ (u ^ (1 / 10 : ℝ))⁻¹ := by positivity
  calc (16 * π ^ 2) ^ (1 / 20 : ℝ) * (Y ^ 4) ^ (1 / 20 : ℝ) * (u ^ (1 / 10 : ℝ))⁻¹
      ≤ 2 * Y * (u ^ (1 / 10 : ℝ))⁻¹ := by gcongr
    _ = _ := rfl

lemma Er_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : Er r ≤ 2 * r ^ (1 / 20 : ℝ) := by
  unfold Er
  have : r ^ (1 / 6 : ℝ) ≤ r ^ (1 / 20 : ℝ) := Real.rpow_le_rpow_of_exponent_ge' hr0 hr1 (by norm_num) (by norm_num)
  linarith

set_option maxHeartbeats 1000000 in
/-- **The pointwise diagonal evaluation.** -/
theorem diag_pointwise : ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (y : ℕ) (u v : ℝ), 1 ≤ y → 40 ≤ u → v ≠ 0 →
    |v| ≤ 1 → 16 * π ^ 2 * (y : ℝ) ^ 4 ≤ u ^ 2 →
      |DiagLag (HafnerMV2.βSel y) y u v - 2 * (Av y v (Real.log (u / (2 * π)))).re| ≤
        C * (|v| * ‖Sv y v‖ + (y : ℝ) ^ N * u ^ (-(1 / 10 : ℝ))) := by
  obtain ⟨Z₀, M, hZ₀, hM1, hInv⟩ := twisted_eval
  obtain ⟨K₂, hK₂⟩ := pow_unbounded_of_one_lt M (by norm_num : (1:ℝ) < 2)
  obtain ⟨K₁, hS⟩ := S_bounds
  obtain ⟨CU, hCU0, hCU⟩ := phase_U
  obtain ⟨CP, hCP0, hCP⟩ := phase_Phi
  obtain ⟨Cε, hCε0, hCε⟩ := eps_bound
  set N := 4 * K₁ + 4 * K₂ + 15
  refine ⟨2 * (4 * Z₀ + |c0| * CP + CU * (|c0| + |gammaD|)) + 2 * Cε, N, by positivity,
    fun y u v hy hu hv0 hv hyu => ?_⟩
  have hu0 : 0 < u := by linarith
  have hY : (1:ℝ) ≤ y := by exact_mod_cast hy
  have hvpos : 0 < |v| := abs_pos.2 hv0
  set S : ℝ := (y : ℝ) ^ (4 * K₁ + 14)
  set W : ℝ := (y : ℝ) ^ N * u ^ (-(1 / 10 : ℝ))
  have hW0 : 0 ≤ W := by positivity
  have hinvu : 1 / u ≤ u ^ (-(1 / 10 : ℝ)) := by
    rw [Real.rpow_neg hu0.le, one_div]
    exact inv_anti₀ (by positivity) (Real.rpow_le_self_of_one_le (by linarith) (by norm_num))
  have hSW : S / u ≤ W := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (pow_le_pow_right₀ hY (by omega)) hinvu (by positivity) (by positivity)
  -- the twisted-sum errors
  set E := sum4 y (fun a b c d => (kap y a b c d : ℂ) * SelbergKey.ev a b c d v *
    (Bs u v (Q1 a b c d) (P1 a b c d) (4 * π ^ 2 * ((P1 a b c d * Q1 a b c d : ℕ) : ℝ)) -
      Mn u v (Q1 a b c d) (P1 a b c d) (4 * π ^ 2 * ((P1 a b c d * Q1 a b c d : ℕ) : ℝ))))
  have hE : ‖E‖ ≤ 4 * Z₀ * W := by
    refine (norm_sum4_le y _ (B := (y : ℝ) ^ 2 * (Z₀ * ((y : ℝ) ^ (4 * K₂ + 8)) * (2 * (2 * y * u ^ (-(1 / 10 : ℝ))))))
      fun a ha b hb c hc d hd => ?_).trans ?_
    · have ha1 := (Finset.mem_Icc.1 ha).1
      have hb1 := (Finset.mem_Icc.1 hb).1
      have hc1 := (Finset.mem_Icc.1 hc).1
      have hd1 := (Finset.mem_Icc.1 hd).1
      have hP := SelbergKeyDiag.P1_pos ha1 hb1 hc1 hd1
      have hQ := SelbergKeyDiag.Q1_pos ha1 hb1 hc1 hd1
      have hcop := (SelbergKeyDiag.coprime_P1_Q1 ha1 hb1 hc1 hd1).symm
      have hPy := P1_le_sq (b := b) (d := d) ha hc
      have hQy := Q1_le_sq (a := a) (c := c) hb hd
      set α := 4 * π ^ 2 * ((P1 a b c d * Q1 a b c d : ℕ) : ℝ)
      have hα : 0 < α := by positivity
      have h1 := hInv (Q1 a b c d) (P1 a b c d) hQ hP hcop u v α hα hv0 hv
      have hev : ‖SelbergKey.ev a b c d v‖ = 1 := by
        unfold SelbergKey.ev
        rw [show (v : ℂ) * I * _ = ((v * (Real.log (P1 a b c d) + Real.log d - Real.log c) : ℝ) : ℂ) * I by
          push_cast; ring]
        exact Complex.norm_exp_ofReal_mul_I _
      rw [norm_mul, norm_mul, hev, mul_one, Complex.norm_real, Real.norm_eq_abs]
      have hQP : 1 ≤ Q1 a b c d * P1 a b c d := Nat.mul_pos hQ hP
      have hQPy : (((Q1 a b c d * P1 a b c d : ℕ) : ℝ)) ≤ (y : ℝ) ^ 4 := by
        have : Q1 a b c d * P1 a b c d ≤ y ^ 2 * y ^ 2 := Nat.mul_le_mul hQy hPy
        calc (((Q1 a b c d * P1 a b c d : ℕ) : ℝ)) ≤ ((y ^ 2 * y ^ 2 : ℕ) : ℝ) := by exact_mod_cast this
          _ = (y : ℝ) ^ 4 := by push_cast; ring
      have hMw : M ^ (Q1 a b c d * P1 a b c d).primeFactors.card * ((Q1 a b c d * P1 a b c d : ℕ) : ℝ) ^ 2 ≤
          (y : ℝ) ^ (4 * K₂ + 8) := by
        have := pow_card_pf_le (by linarith) hK₂.le hQP
        calc _ ≤ ((Q1 a b c d * P1 a b c d : ℕ) : ℝ) ^ K₂ * ((Q1 a b c d * P1 a b c d : ℕ) : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_right this (by positivity)
          _ ≤ ((y : ℝ) ^ 4) ^ K₂ * ((y : ℝ) ^ 4) ^ 2 := by gcongr
          _ = (y : ℝ) ^ (4 * K₂ + 8) := by rw [← pow_mul, ← pow_mul, ← pow_add]
      -- `r = α/TT ≤ 16π²y⁴/u² ≤ 1`
      have hTT := TT_ge (u := u) (by linarith) hv
      have hr0 : 0 ≤ α / TT u v := (div_pos hα (TT_pos u v)).le
      have hPQy : ((P1 a b c d * Q1 a b c d : ℕ) : ℝ) ≤ (y : ℝ) ^ 4 := by
        rw [Nat.mul_comm]; exact hQPy
      have hαy : α ≤ 4 * π ^ 2 * (y : ℝ) ^ 4 := mul_le_mul_of_nonneg_left hPQy (by positivity)
      have hr : α / TT u v ≤ 16 * π ^ 2 * (y : ℝ) ^ 4 / u ^ 2 := by
        rw [div_le_div_iff₀ (TT_pos u v) (by positivity)]
        calc α * u ^ 2 ≤ 4 * π ^ 2 * (y : ℝ) ^ 4 * u ^ 2 := mul_le_mul_of_nonneg_right hαy (by positivity)
          _ = 16 * π ^ 2 * (y : ℝ) ^ 4 * (u ^ 2 / 4) := by ring
          _ ≤ 16 * π ^ 2 * (y : ℝ) ^ 4 * TT u v := mul_le_mul_of_nonneg_left hTT (by positivity)
      have hr1 : α / TT u v ≤ 1 := hr.trans (by rw [div_le_one (by positivity)]; exact hyu)
      have hEr := (Er_le hr0 hr1).trans (mul_le_mul_of_nonneg_left (rpow20_le hY hu0 hr0 hr) (by norm_num))
      have hκ := abs_kap_le ha hb hc hd
      calc |kap y a b c d| * ‖Bs u v (Q1 a b c d) (P1 a b c d) α - Mn u v (Q1 a b c d) (P1 a b c d) α‖
          ≤ (y : ℝ) ^ 2 * (Z₀ * (y : ℝ) ^ (4 * K₂ + 8) * (2 * (2 * y * u ^ (-(1 / 10 : ℝ))))) := by
            refine mul_le_mul hκ (h1.trans ?_) (norm_nonneg _) (by positivity)
            refine mul_le_mul ?_ hEr (Er_nonneg hr0) (by positivity)
            calc Z₀ * M ^ (Q1 a b c d * P1 a b c d).primeFactors.card * ((Q1 a b c d * P1 a b c d : ℕ) : ℝ) ^ 2
                = Z₀ * (M ^ (Q1 a b c d * P1 a b c d).primeFactors.card *
                    ((Q1 a b c d * P1 a b c d : ℕ) : ℝ) ^ 2) := by ring
              _ ≤ Z₀ * (y : ℝ) ^ (4 * K₂ + 8) := mul_le_mul_of_nonneg_left hMw hZ₀
        _ = _ := rfl
    · have hyN : (y : ℝ) ^ 4 * ((y : ℝ) ^ 2 * (y : ℝ) ^ (4 * K₂ + 8) * (y : ℝ)) ≤ (y : ℝ) ^ N := by
        rw [← pow_add, ← pow_succ, ← pow_add]
        exact pow_le_pow_right₀ hY (by omega)
      calc (y : ℝ) ^ 4 * ((y : ℝ) ^ 2 * (Z₀ * (y : ℝ) ^ (4 * K₂ + 8) * (2 * (2 * y * u ^ (-(1 / 10 : ℝ))))))
          = 4 * Z₀ * ((y : ℝ) ^ 4 * ((y : ℝ) ^ 2 * (y : ℝ) ^ (4 * K₂ + 8) * (y : ℝ))) * u ^ (-(1 / 10 : ℝ)) := by
            ring
        _ ≤ 4 * Z₀ * (y : ℝ) ^ N * u ^ (-(1 / 10 : ℝ)) := by gcongr
        _ = 4 * Z₀ * W := by ring
  -- the main-term difference
  have hX : ‖Ush u (u + v) * Xm u v y - Av y v (Real.log (u / (2 * π)))‖ ≤
      (|c0| * CP + CU * (|c0| + |gammaD|)) * W + Cε * (|v| * ‖Sv y v‖) := by
    rw [UXm_sub_Av]
    obtain ⟨hS0, hS1⟩ := hS y v
    have hU1 : ‖Ush u (u + v)‖ = 1 := norm_Ush u (u + v)
    have hvI : ‖(v : ℂ) * I‖ = |v| := by rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hP := hCP u v hu hv
    have hUU := hCU u v (by linarith) hv
    have he : ‖((Real.exp (-(v / 2) ^ 2) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg (v / 2)])
    have t1 : ‖(c0 : ℂ) * (Real.exp (-(v / 2) ^ 2) : ℂ) / ((v : ℂ) * I) *
        (Ush u (u + v) * Gsh u (u + v) (pv v) * ((4 * π ^ 2 : ℝ) : ℂ) ^ (-pv v) - 1) * S0v y v‖ ≤
        |c0| * CP * (S / u) := by
      have hP' : ‖Ush u (u + v) * Gsh u (u + v) (pv v) * ((4 * π ^ 2 : ℝ) : ℂ) ^ (-pv v) - 1‖ ≤ CP * v ^ 2 / u := hP
      have hn : ‖(c0 : ℂ) * (Real.exp (-(v / 2) ^ 2) : ℂ) / ((v : ℂ) * I) *
          (Ush u (u + v) * Gsh u (u + v) (pv v) * ((4 * π ^ 2 : ℝ) : ℂ) ^ (-pv v) - 1) * S0v y v‖ =
          |c0| * ‖((Real.exp (-(v / 2) ^ 2) : ℝ) : ℂ)‖ / |v| *
            ‖Ush u (u + v) * Gsh u (u + v) (pv v) * ((4 * π ^ 2 : ℝ) : ℂ) ^ (-pv v) - 1‖ * ‖S0v y v‖ := by
        rw [norm_mul, norm_mul, norm_div, norm_mul, hvI, Complex.norm_real, Real.norm_eq_abs]
      rw [hn]
      calc |c0| * ‖((Real.exp (-(v / 2) ^ 2) : ℝ) : ℂ)‖ / |v| *
            ‖Ush u (u + v) * Gsh u (u + v) (pv v) * ((4 * π ^ 2 : ℝ) : ℂ) ^ (-pv v) - 1‖ * ‖S0v y v‖
          ≤ |c0| * 1 / |v| * (CP * v ^ 2 / u) * S := by gcongr
        _ = |c0| * CP * (|v| * S / u) := by
            rw [← sq_abs v]; field_simp
        _ ≤ |c0| * CP * (S / u) := by
            gcongr
            exact mul_le_of_le_one_left (by positivity) hv
    have t2 : ‖(Ush u (u + v) - cexp (-((v * Real.log (u / (2 * π)) : ℝ) : ℂ) * I)) *
        (-(c0 : ℂ) / ((v : ℂ) * I) + gammaD) * Sv y v‖ ≤ CU * (|c0| + |gammaD|) * (S / u) := by
      rw [norm_mul, norm_mul]
      have hL : ‖-(c0 : ℂ) / ((v : ℂ) * I) + gammaD‖ ≤ |c0| / |v| + |gammaD| := by
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_div, norm_neg, hvI, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      calc ‖Ush u (u + v) - cexp (-((v * Real.log (u / (2 * π)) : ℝ) : ℂ) * I)‖ *
            ‖-(c0 : ℂ) / ((v : ℂ) * I) + gammaD‖ * ‖Sv y v‖
          ≤ (CU * |v| / u) * (|c0| / |v| + |gammaD|) * S := by gcongr
        _ = CU * (|c0| + |gammaD| * |v|) * (S / u) := by field_simp
        _ ≤ CU * (|c0| + |gammaD|) * (S / u) := by
            gcongr
            calc |gammaD| * |v| ≤ |gammaD| * 1 := by gcongr
              _ = |gammaD| := mul_one _
    have t3 : ‖Ush u (u + v) * ((v : ℂ) * I * epsv v) * Sv y v‖ ≤ Cε * (|v| * ‖Sv y v‖) := by
      rw [norm_mul, norm_mul, norm_mul, hU1, hvI]
      calc 1 * (|v| * ‖epsv v‖) * ‖Sv y v‖ ≤ 1 * (|v| * Cε) * ‖Sv y v‖ := by gcongr; exact hCε v
        _ = _ := by ring
    calc _ ≤ ‖(c0 : ℂ) * (Real.exp (-(v / 2) ^ 2) : ℂ) / ((v : ℂ) * I) *
          (Ush u (u + v) * Gsh u (u + v) (pv v) * ((4 * π ^ 2 : ℝ) : ℂ) ^ (-pv v) - 1) * S0v y v‖ +
        ‖(Ush u (u + v) - cexp (-((v * Real.log (u / (2 * π)) : ℝ) : ℂ) * I)) *
          (-(c0 : ℂ) / ((v : ℂ) * I) + gammaD) * Sv y v‖ +
        ‖Ush u (u + v) * ((v : ℂ) * I * epsv v) * Sv y v‖ := norm_sub_le_of_le (norm_add_le _ _) le_rfl
      _ ≤ |c0| * CP * (S / u) + CU * (|c0| + |gammaD|) * (S / u) + Cε * (|v| * ‖Sv y v‖) :=
          add_le_add (add_le_add t1 t2) t3
      _ = (|c0| * CP + CU * (|c0| + |gammaD|)) * (S / u) + Cε * (|v| * ‖Sv y v‖) := by ring
      _ ≤ _ := by
          have h0 : 0 ≤ |c0| * CP + CU * (|c0| + |gammaD|) := by positivity
          have := mul_le_mul_of_nonneg_left hSW h0
          linarith
  -- combine
  rw [diagLag_eq]
  have hcomb : 2 * (Ush u (u + v) * (E + Xm u v y)).re - 2 * (Av y v (Real.log (u / (2 * π)))).re =
      2 * ((Ush u (u + v) * E) + (Ush u (u + v) * Xm u v y - Av y v (Real.log (u / (2 * π))))).re := by
    simp only [Complex.add_re, Complex.sub_re, mul_add]; ring
  rw [hcomb, abs_mul, abs_two]
  have h1 : |((Ush u (u + v) * E) + (Ush u (u + v) * Xm u v y - Av y v (Real.log (u / (2 * π))))).re| ≤
      ‖E‖ + ‖Ush u (u + v) * Xm u v y - Av y v (Real.log (u / (2 * π)))‖ := by
    refine (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans (le_of_eq ?_))
    rw [norm_mul, norm_Ush, one_mul]
  have hfin := h1.trans (add_le_add hE hX)
  have hvS : 0 ≤ |v| * ‖Sv y v‖ := by positivity
  set X := |c0| * CP + CU * (|c0| + |gammaD|)
  have hX0 : 0 ≤ X := by positivity
  calc 2 * |((Ush u (u + v) * E) + (Ush u (u + v) * Xm u v y - Av y v (Real.log (u / (2 * π))))).re|
      ≤ 2 * (4 * Z₀ * W + (X * W + Cε * (|v| * ‖Sv y v‖))) := by linarith
    _ = 2 * (4 * Z₀ + X) * W + 2 * Cε * (|v| * ‖Sv y v‖) := by ring
    _ ≤ (2 * (4 * Z₀ + X) + 2 * Cε) * W + (2 * (4 * Z₀ + X) + 2 * Cε) * (|v| * ‖Sv y v‖) := by
        gcongr <;> nlinarith
    _ = _ := by ring

end RamanujanTau.SelbergKeyDiag2
