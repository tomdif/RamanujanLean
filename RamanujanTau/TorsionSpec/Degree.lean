import RamanujanTau.HeightEll.Seq

/-!
# Exact degrees of the multiplication-by-`n` abscissa (polynomial core)

For `y² = x³ + ax + b` over an algebraically closed field `k` of characteristic `0` with
`4a³ + 27b² ≠ 0`: if `X_{m}`, `X_{m+1}` are given by coprime `c/d` with `deg c = n²`,
`deg d = n² − 1`, `lc d = n² lc c`, and `X_{m+2}` satisfies the Kummer relations
`E (X_{m+2} + X_m) = S`, `E X_{m+2} X_m = Q`, then so is `X_{m+2}` (**`deg_step`**).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TorsionSpec

open Polynomial

variable {k : Type*} [Field k]

/-- `(c − X d)²`. -/
noncomputable def Ep (c d : k[X]) : k[X] := (c - X * d) ^ 2

/-- homogenised `x(P+Q) + x(P−Q)` numerator at `(c/d, X)`. -/
noncomputable def Sp (a b : k) (c d : k[X]) : k[X] :=
  2 * c * X * (c + X * d) + C (2 * a) * (c * d + X * d ^ 2) + C (4 * b) * d ^ 2

/-- homogenised `x(P+Q) x(P−Q)` numerator at `(c/d, X)`. -/
noncomputable def Qp (a b : k) (c d : k[X]) : k[X] :=
  c ^ 2 * X ^ 2 - C (2 * a) * c * X * d - C (4 * b) * (c * d + X * d ^ 2) + C (a ^ 2) * d ^ 2

variable [CharZero k]

lemma common_root_Δ {a b : k} (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) {c d : k[X]} (hcd : IsCoprime c d)
    (z : k) (hE : (Ep c d).eval z = 0) (hS : (Sp a b c d).eval z = 0)
    (hQ : (Qp a b c d).eval z = 0) : False := by
  simp only [Ep, Sp, Qp, eval_pow, eval_sub, eval_mul, eval_X, eval_add, eval_C, eval_ofNat]
    at hE hS hQ
  have hc : c.eval z = z * d.eval z := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hE; linear_combination this
  by_cases hδ : d.eval z = 0
  · obtain ⟨u, v, huv⟩ := hcd
    have := congrArg (eval z) huv
    simp only [eval_add, eval_mul, eval_one] at this
    rw [hc, hδ] at this; simp at this
  · rw [hc] at hS hQ
    have hδ2 : d.eval z ^ 2 ≠ 0 := pow_ne_zero 2 hδ
    have h1 : z ^ 3 + a * z + b = 0 := by
      have : d.eval z ^ 2 * (4 * (z ^ 3 + a * z + b)) = 0 := by linear_combination hS
      have := (mul_eq_zero.1 this).resolve_left hδ2
      exact (mul_eq_zero.1 this).resolve_left (by norm_num)
    have h2 : z ^ 4 - 2 * a * z ^ 2 - 8 * b * z + a ^ 2 = 0 := by
      have : d.eval z ^ 2 * (z ^ 4 - 2 * a * z ^ 2 - 8 * b * z + a ^ 2) = 0 := by
        linear_combination hQ
      exact (mul_eq_zero.1 this).resolve_left hδ2
    exact hΔ (by linear_combination (27 * b + 5 * a * z - 3 * z ^ 3) * h1 + (4 * a + 3 * z ^ 2) * h2)

variable [IsAlgClosed k]

theorem deg_step {a b : k} (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) {m : ℕ} (hm : 1 ≤ m)
    {c d cm dm cp dp : k[X]}
    (hcd : IsCoprime c d) (hc : c.natDegree = (m + 1) ^ 2) (hd : d.natDegree + 1 = (m + 1) ^ 2)
    (hd0 : d ≠ 0) (hl : c.leadingCoeff * ((m : k) + 1) ^ 2 = d.leadingCoeff)
    (hcdm : IsCoprime cm dm) (hcm : cm.natDegree = m ^ 2) (hdm : dm.natDegree + 1 = m ^ 2)
    (hdm0 : dm ≠ 0) (hlm : cm.leadingCoeff * (m : k) ^ 2 = dm.leadingCoeff)
    (hcdp : IsCoprime cp dp) (hdp0 : dp ≠ 0)
    (hsum : Ep c d * (cp * dm + cm * dp) = Sp a b c d * (dp * dm))
    (hprod : Ep c d * (cp * cm) = Qp a b c d * (dp * dm)) :
    cp.natDegree = (m + 2) ^ 2 ∧ dp.natDegree + 1 = (m + 2) ^ 2 ∧
      cp.leadingCoeff * ((m : k) + 2) ^ 2 = dp.leadingCoeff := by
  have hm0 : (m : k) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hm2 : (m : k) + 2 ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
  have hc0 : c ≠ 0 := by
    rintro rfl; rw [natDegree_zero] at hc; have := pow_pos (show 0 < m + 1 by omega) 2
    omega
  have hcm0 : cm ≠ 0 := by
    rintro rfl; rw [natDegree_zero] at hcm; have := pow_pos (show 0 < m by omega) 2
    omega
  have hL : c.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hc0
  have hLm : cm.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hcm0
  -- the polynomial `c − X d`
  have hXd0 : X * d ≠ 0 := mul_ne_zero X_ne_zero hd0
  have hXd : (X * d).natDegree = (m + 1) ^ 2 := by
    rw [natDegree_mul X_ne_zero hd0, natDegree_X]; omega
  have hXdl : (X * d).leadingCoeff = d.leadingCoeff := by simp
  have hne : c.leadingCoeff ≠ d.leadingCoeff := by
    rw [← hl]; intro h
    have : c.leadingCoeff * ((m : k) * ((m : k) + 2)) = 0 := by linear_combination -h
    exact mul_ne_zero hL (mul_ne_zero hm0 hm2) this
  have hdeg_eq : c.degree = (X * d).degree := by
    rw [degree_eq_natDegree hc0, degree_eq_natDegree hXd0, hc, hXd]
  have hsub_lc : (c - X * d).leadingCoeff = c.leadingCoeff - d.leadingCoeff := by
    rw [leadingCoeff_sub_of_degree_eq hdeg_eq (by rwa [hXdl]), hXdl]
  have hsub0 : c - X * d ≠ 0 := by
    intro h; rw [h, leadingCoeff_zero] at hsub_lc; exact hne (sub_eq_zero.1 hsub_lc.symm)
  have hsub_deg : (c - X * d).natDegree = (m + 1) ^ 2 := by
    apply le_antisymm
    · exact (natDegree_sub_le _ _).trans (by rw [hc, hXd, max_self])
    · apply le_natDegree_of_ne_zero
      rw [coeff_sub, ← hc, coeff_natDegree, hc, ← hXd, coeff_natDegree, hXdl]
      exact sub_ne_zero.2 hne
  have hE0 : Ep c d ≠ 0 := pow_ne_zero 2 hsub0
  have hEdeg : (Ep c d).natDegree = 2 * (m + 1) ^ 2 := by
    rw [Ep, natDegree_pow, hsub_deg]
  have hElc : (Ep c d).leadingCoeff = (c.leadingCoeff - d.leadingCoeff) ^ 2 := by
    rw [Ep, leadingCoeff_pow, hsub_lc]
  -- the polynomial `Qp`
  set R := C (2 * a) * c * X * d + C (4 * b) * (c * d + X * d ^ 2) - C (a ^ 2) * d ^ 2 with hR
  have hQp : Qp a b c d = c ^ 2 * X ^ 2 - R := by rw [Qp, hR]; ring
  have hc2 : (c ^ 2 * X ^ 2).natDegree = 2 * (m + 1) ^ 2 + 2 := by
    rw [natDegree_mul (pow_ne_zero 2 hc0) (pow_ne_zero 2 X_ne_zero), natDegree_pow, natDegree_pow,
      natDegree_X, hc]
  have hRdeg : R.natDegree < 2 * (m + 1) ^ 2 + 2 := by
    generalize hN : (m + 1) ^ 2 = N at hc hd
    have t1 : (C (2 * a) * c * X * d).natDegree ≤ 2 * N := by
      refine natDegree_mul_le.trans ?_
      have := (natDegree_mul_le (p := C (2 * a) * c) (q := X)).trans
        (add_le_add ((natDegree_mul_le).trans (add_le_add (natDegree_C (2 * a)).le le_rfl))
          natDegree_X_le)
      omega
    have t2 : (c * d).natDegree ≤ 2 * N := natDegree_mul_le.trans (by omega)
    have t3 : (X * d ^ 2).natDegree ≤ 2 * N := by
      refine natDegree_mul_le.trans ?_
      have := natDegree_X_le (R := k)
      have := natDegree_pow_le (p := d) (n := 2)
      omega
    have t4 : (d ^ 2).natDegree ≤ 2 * N := by
      have := natDegree_pow_le (p := d) (n := 2); omega
    have t5 : (C (4 * b) * (c * d + X * d ^ 2)).natDegree ≤ 2 * N :=
      (natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans (max_le t2 t3))
    have t6 : (C (a ^ 2) * d ^ 2).natDegree ≤ 2 * N := (natDegree_C_mul_le _ _).trans t4
    have : R.natDegree ≤ 2 * N := by
      rw [hR]
      exact (natDegree_sub_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le t1 t5)) t6)
    omega
  have hQdeg : (Qp a b c d).natDegree = 2 * (m + 1) ^ 2 + 2 := by
    rw [hQp, natDegree_sub_eq_left_of_natDegree_lt (hc2 ▸ hRdeg), hc2]
  have hQlc : (Qp a b c d).leadingCoeff = c.leadingCoeff ^ 2 := by
    rw [hQp, leadingCoeff_sub_of_degree_lt, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow,
      leadingCoeff_X, one_pow, mul_one]
    rw [degree_eq_natDegree (mul_ne_zero (pow_ne_zero 2 hc0) (pow_ne_zero 2 X_ne_zero)), hc2]
    by_cases hR0 : R = 0
    · rw [hR0, degree_zero]; exact WithBot.bot_lt_coe _
    · rw [degree_eq_natDegree hR0]; exact_mod_cast hRdeg
  have hQ0 : Qp a b c d ≠ 0 := by
    intro h; rw [h, leadingCoeff_zero] at hQlc; exact hL (pow_eq_zero_iff two_ne_zero |>.1 hQlc.symm)
  -- the Gauss step
  have hdiv : dp * dm ∣ Ep c d :=
    HeightEll.dvd_core hcdp hcdm ⟨Qp a b c d, by rw [hprod]; ring⟩
      ⟨Sp a b c d, by rw [hsum]; ring⟩
  obtain ⟨e, he⟩ := hdiv
  have hdd : dp * dm ≠ 0 := mul_ne_zero hdp0 hdm0
  have hQe : e * (cp * cm) = Qp a b c d := by
    apply mul_left_cancel₀ hdd
    linear_combination (cp * cm) * he.symm + hprod
  have hSe : e * (cp * dm + cm * dp) = Sp a b c d := by
    apply mul_left_cancel₀ hdd
    linear_combination (cp * dm + cm * dp) * he.symm + hsum
  have he0 : e ≠ 0 := by rintro rfl; rw [mul_zero] at he; exact hE0 he
  have hedeg : e.natDegree = 0 := by
    by_contra h
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root e (by
      rw [degree_eq_natDegree he0]; exact_mod_cast h)
    have hz' : e.eval z = 0 := hz
    apply common_root_Δ hΔ hcd z
    · rw [he, eval_mul, hz', mul_zero]
    · rw [← hSe, eval_mul, hz', zero_mul]
    · rw [← hQe, eval_mul, hz', zero_mul]
  have hcp0 : cp ≠ 0 := by rintro rfl; rw [zero_mul, mul_zero] at hQe; exact hQ0 hQe.symm
  -- degrees
  have h1 := congrArg natDegree he
  rw [natDegree_mul hdd he0, natDegree_mul hdp0 hdm0, hEdeg, hedeg] at h1
  have h2 := congrArg natDegree hQe
  rw [natDegree_mul he0 (mul_ne_zero hcp0 hcm0), natDegree_mul hcp0 hcm0, hQdeg, hedeg, hcm] at h2
  have e1 : (m + 2) ^ 2 + m ^ 2 = 2 * (m + 1) ^ 2 + 2 := by ring
  refine ⟨by omega, by omega, ?_⟩
  -- leading coefficients
  have l1 := congrArg leadingCoeff he
  rw [leadingCoeff_mul, leadingCoeff_mul, hElc] at l1
  have l2 := congrArg leadingCoeff hQe
  rw [leadingCoeff_mul, leadingCoeff_mul, hQlc] at l2
  have hμ : e.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 he0
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hμ hLm) (pow_ne_zero 2 hm0))
  rw [← hl] at l1
  rw [← hlm] at l1
  linear_combination (((m : k) + 2) ^ 2 * (m : k) ^ 2) * l2 + l1

/-! ### Application to the universal sequence `Xₙ` -/

open HeightEll

/-- `Xₙ = c/d` with `c, d` coprime, `deg c = n²`, `deg d = n² − 1`, `lc d = n² lc c`. -/
def Good (W : WeierstrassCurve k) (n : ℕ) : Prop :=
  ∃ c d : k[X], IsCoprime c d ∧ d ≠ 0 ∧
    Xs W n = algebraMap k[X] (RatFunc k) c / algebraMap k[X] (RatFunc k) d ∧
    c.natDegree = n ^ 2 ∧ d.natDegree + 1 = n ^ 2 ∧ c.leadingCoeff * (n : k) ^ 2 = d.leadingCoeff

variable {W : WeierstrassCurve k} {a b : k} (hb₂ : W.b₂ = 0) (hb₄ : W.b₄ = 2 * a)
  (hb₆ : W.b₆ = 4 * b) (hb₈ : W.b₈ = -a ^ 2) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0)
include hb₂ hb₄ hb₆ hb₈ hΔ

lemma good_one : Good W 1 :=
  ⟨X, 1, isCoprime_one_right, one_ne_zero, by simp [Xs, tX], by simp, by simp, by simp⟩

lemma kPhi_C : kPhi (W.map C) (X : k[X]) =
    X ^ 4 - C (2 * a) * X ^ 2 - C (8 * b) * X + C (a ^ 2) := by
  simp only [kPhi, WeierstrassCurve.map_b₄, WeierstrassCurve.map_b₆, WeierstrassCurve.map_b₈,
    hb₄, hb₆, hb₈, map_neg, map_mul, map_pow, map_ofNat]
  ring

lemma kPsi_C : kPsi (W.map C) (X : k[X]) = C 4 * X ^ 3 + C (4 * a) * X + C (4 * b) := by
  simp only [kPsi, WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄, WeierstrassCurve.map_b₆,
    hb₂, hb₄, hb₆, map_zero, map_mul, map_ofNat]
  ring

lemma good_two : Good W 2 := by
  refine ⟨X ^ 4 - C (2 * a) * X ^ 2 - C (8 * b) * X + C (a ^ 2),
    C 4 * X ^ 3 + C (4 * a) * X + C (4 * b), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed k k]
    intro z
    by_contra h
    push Not at h
    obtain ⟨h1, h2⟩ := h
    simp only [aeval_X, map_add, map_sub, map_mul, map_pow, aeval_C, Algebra.algebraMap_self,
      RingHom.id_apply] at h1 h2
    apply hΔ
    have h2' : z ^ 3 + a * z + b = 0 := by linear_combination h2 / 4
    have h1' : z ^ 4 - 2 * a * z ^ 2 - 8 * b * z + a ^ 2 = 0 := by linear_combination h1
    linear_combination (27 * b + 5 * a * z - 3 * z ^ 3) * h2' + (4 * a + 3 * z ^ 2) * h1'
  · intro h
    have := congrArg (coeff · 3) h
    simp at this
  · simp only [Xs, Wr_eq, ← map_kPhi, ← map_kPsi, tX]
    rw [kPhi_C hb₂ hb₄ hb₆ hb₈ hΔ, kPsi_C hb₂ hb₄ hb₆ hb₈ hΔ]
  · compute_degree!
  · have : (C 4 * X ^ 3 + C (4 * a) * X + C (4 * b) : k[X]).natDegree = 3 := by compute_degree!
    rw [this]; norm_num
  · have h1 : (X ^ 4 - C (2 * a) * X ^ 2 - C (8 * b) * X + C (a ^ 2) : k[X]).leadingCoeff = 1 := by
      apply Monic.leadingCoeff; monicity!
    have h2 : (C 4 * X ^ 3 + C (4 * a) * X + C (4 * b) : k[X]).leadingCoeff = 4 := by
      rw [leadingCoeff, show (C 4 * X ^ 3 + C (4 * a) * X + C (4 * b) : k[X]).natDegree = 3 by
        compute_degree!]
      simp
    rw [h1, h2]; norm_num

lemma good_succ (m : ℕ) (hne : Xs W (m + 2) ≠ tX)
    (hrel : (Xs W (m + 2) - tX) ^ 2 * (Xs W (m + 3) * Xs W (m + 1)) = kQ (Wr W) (Xs W (m + 2)) tX)
    (h1 : Good W (m + 1)) (h2 : Good W (m + 2)) : Good W (m + 3) := by
  obtain ⟨cm, dm, hcdm, hdm0, hXm, hcm, hdm, hlm⟩ := h1
  obtain ⟨c, d, hcd, hd0, hX, hc, hd, hl⟩ := h2
  set I := algebraMap k[X] (RatFunc k) with hI
  set x := Xs W (m + 3)
  have hXp : x = I x.num / I x.denom := (RatFunc.num_div_denom x).symm
  have hdpI : I x.denom ≠ 0 := RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero x)
  have hdmI : I dm ≠ 0 := RatFunc.algebraMap_ne_zero hdm0
  have hdI : I d ≠ 0 := RatFunc.algebraMap_ne_zero hd0
  have hb₂' : (Wr W).b₂ = 0 := by rw [WeierstrassCurve.map_b₂, hb₂, map_zero]
  have hb₄' : (Wr W).b₄ = I (C (2 * a)) := by rw [WeierstrassCurve.map_b₄, hb₄]; rfl
  have hb₆' : (Wr W).b₆ = I (C (4 * b)) := by rw [WeierstrassCurve.map_b₆, hb₆]; rfl
  have hb₈' : (Wr W).b₈ = -I (C (a ^ 2)) := by
    rw [WeierstrassCurve.map_b₈, hb₈, map_neg]; rfl
  have hsumR : (Xs W (m + 2) - tX) ^ 2 * (x + Xs W (m + 1)) = kS (Wr W) (Xs W (m + 2)) tX := by
    have hx0 : (Xs W (m + 2) - tX) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.2 hne)
    show (Xs W (m + 2) - tX) ^ 2 * (kS (Wr W) (Xs W (m + 2)) tX / (Xs W (m + 2) - tX) ^ 2 -
      Xs W (m + 1) + Xs W (m + 1)) = _
    rw [sub_add_cancel, mul_div_assoc', mul_div_cancel_left₀ _ hx0]
  have htX : tX = I X := rfl
  rw [hX, hXm, hXp, htX] at hsumR hrel
  rw [hX, htX] at hne
  rw [kS, hb₂', hb₄', hb₆'] at hsumR
  rw [kQ, hb₄', hb₆', hb₈'] at hrel
  have hsum : Ep c d * (x.num * dm + cm * x.denom) = Sp a b c d * (x.denom * dm) := by
    apply RatFunc.algebraMap_injective
    rw [← hI]
    simp only [Ep, Sp, map_mul, map_add, map_sub, map_pow, map_ofNat]
    field_simp at hsumR
    simp only [map_mul, map_pow, map_ofNat] at hsumR ⊢
    linear_combination hsumR
  have hprod : Ep c d * (x.num * cm) = Qp a b c d * (x.denom * dm) := by
    apply RatFunc.algebraMap_injective
    rw [← hI]
    simp only [Ep, Qp, map_mul, map_add, map_sub, map_pow, map_ofNat]
    field_simp at hrel
    simp only [map_mul, map_pow, map_ofNat] at hrel ⊢
    linear_combination hrel
  have hm1 : 1 ≤ m + 1 := by omega
  obtain ⟨r1, r2, r3⟩ := deg_step hΔ hm1 hcd (by rw [hc]) (by rw [hd]) hd0
    (by rw [← hl]; push_cast; ring) hcdm hcm hdm hdm0 (by rw [← hlm])
    (RatFunc.isCoprime_num_denom x) (RatFunc.denom_ne_zero x) hsum hprod
  refine ⟨x.num, x.denom, RatFunc.isCoprime_num_denom x, RatFunc.denom_ne_zero x, hXp,
    by rw [r1], by rw [r2], ?_⟩
  rw [← r3]; push_cast; ring

theorem good_all (hne : ∀ m, Xs W (m + 2) ≠ tX)
    (hrel : ∀ m, (Xs W (m + 2) - tX) ^ 2 * (Xs W (m + 3) * Xs W (m + 1)) =
      kQ (Wr W) (Xs W (m + 2)) tX) :
    ∀ n, 1 ≤ n → Good W n := by
  have key : ∀ m, Good W (m + 1) ∧ Good W (m + 2) := by
    intro m
    induction m with
    | zero => exact ⟨good_one hb₂ hb₄ hb₆ hb₈ hΔ, good_two hb₂ hb₄ hb₆ hb₈ hΔ⟩
    | succ m ih =>
      exact ⟨ih.2, good_succ hb₂ hb₄ hb₆ hb₈ hΔ m (hne m) (hrel m) ih.1 ih.2⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (key m).1

end TorsionSpec
