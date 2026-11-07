/-
# Edge non-vanishing `L(1 + it) ≠ 0`, `t ≠ 0`, for abstract normalized data

Same proof as `EdgeNonvanishing/` (for `Δ`), now from the fields of `EData` only.
`F(σ) = ζ(σ) L(σ+it)² L(σ−it)² (ζ(2σ)R(σ))² ζ(2σ+4it)R(σ+2it) ζ(2σ−4it)R(σ−2it)` is the
Rankin–Selberg L-function of `Π × Π̃`, `Π = 1 ⊞ f|·|^{it} ⊞ f|·|^{−it}`; its Euler factors
are `exp ℓ_p`, `ℓ_p ≥ 0` (`EdgeNonvanishing.localD_inv_eq_exp`), so `‖F(σ)‖ ≥ 1`; a zero at
`1 + it` forces `F(1 + h) = O(h) → 0`.

The real point `t = 0` is **not** covered by this argument (`F` then has pole order 5 and zero
order 4); `L_ne_zero_of_ge` takes `L 1 ≠ 0` as an explicit hypothesis.
-/
import RamanujanTau.EigenformEdge.Data

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanTau.EigenformEdge

open Complex Finset Filter Topology Asymptotics LSeries
open scoped ComplexConjugate
open EData

variable [EData]

/-- The `ζ(2s)R(s)` Euler factor. -/
noncomputable def fR (s : ℂ) (p : ℕ) : ℂ := (1 - (p : ℂ) ^ (-(2 * s)))⁻¹ * ∑' e, term rsB s (p ^ e)

lemma fR_hasProd {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => fR s p) (riemannZeta (2 * s) * RS s) := by
  have h2 : 1 < (2 * s).re := by simp; linarith
  exact (riemannZeta_eulerProduct_hasProd h2).mul (rs_eulerProduct hs)

/-- The points. -/
noncomputable def sL (σ t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * I
noncomputable def sR (σ t : ℝ) : ℂ := (σ : ℂ) + 2 * (t : ℂ) * I

/-- The product `F(σ)`. -/
noncomputable def Fval (σ t : ℝ) : ℂ :=
  riemannZeta σ * (L (sL σ t) * L (sL σ t)) * (L (sL σ (-t)) * L (sL σ (-t))) *
    ((riemannZeta (2 * σ) * RS σ) * (riemannZeta (2 * σ) * RS σ)) *
    (riemannZeta (2 * sR σ t) * RS (sR σ t)) * (riemannZeta (2 * sR σ (-t)) * RS (sR σ (-t)))

/-- The Euler factor of `F`. -/
noncomputable def Fp (σ t : ℝ) (p : ℕ) : ℂ :=
  (1 - (p : ℂ) ^ (-(σ : ℂ)))⁻¹ * ((localPoly (sL σ t) p)⁻¹ * (localPoly (sL σ t) p)⁻¹) *
    ((localPoly (sL σ (-t)) p)⁻¹ * (localPoly (sL σ (-t)) p)⁻¹) *
    (fR σ p * fR σ p) * fR (sR σ t) p * fR (sR σ (-t)) p

lemma Fp_hasProd {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    HasProd (fun p : Nat.Primes => Fp σ t p) (Fval σ t) := by
  have hL : ∀ u : ℝ, 1 < (sL σ u).re := fun u => by simp [sL]; linarith
  have hz := riemannZeta_eulerProduct_hasProd (s := (σ : ℂ)) (by simpa using hσ)
  have ha := L_eulerProduct (hL t)
  have hb := L_eulerProduct (hL (-t))
  have hr0 := fR_hasProd (s := (σ : ℂ)) (by simpa using hσ)
  have hr1 := fR_hasProd (s := sR σ t) (by simp [sR]; linarith)
  have hr2 := fR_hasProd (s := sR σ (-t)) (by simp [sR]; linarith)
  exact ((((hz.mul (ha.mul ha)).mul (hb.mul hb)).mul (hr0.mul hr0)).mul hr1).mul hr2

/-- **Per-prime positivity**: `Fp σ t p = exp ℓ` with `ℓ ≥ 0`. -/
theorem Fp_eq_exp {σ : ℝ} (hσ : 1 < σ) (t : ℝ) {p : ℕ} (hp : p.Prime) :
    ∃ ℓ : ℝ, 0 ≤ ℓ ∧ Fp σ t p = ((Real.exp ℓ : ℝ) : ℂ) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  obtain ⟨α, β, hab, hs, hα1, hβ⟩ := EdgeNonvanishing.satake (lam p)
  have hα := alpha_sq_le hp hab hs hβ
  have hxp : (p : ℝ) * (p : ℝ) ^ (-σ) < 1 := by
    have : (p : ℝ) * (p : ℝ) ^ (-σ) = (p : ℝ) ^ (1 - σ) := by
      rw [Real.rpow_sub (by positivity), Real.rpow_one, Real.rpow_neg (by positivity), div_eq_mul_inv]
    rw [this]; exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  set x : ℝ := (p : ℝ) ^ (-σ)
  have hX : (p : ℂ) ^ (-(σ : ℂ)) = (x : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity)]; push_cast; rfl
  have hx0 : 0 ≤ x := by positivity
  have hαx : ‖α‖ ^ 2 * x < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hα hx0) hxp
  have hZ : ∀ u : ℝ, (p : ℂ) ^ (-(sL σ u)) = EdgeNonvanishing.ep p u * x := by
    intro u
    rw [← hX, EdgeNonvanishing.ep, ← cpow_add _ _ hp0]; congr 1; simp [sL]
  have hY : ∀ u : ℝ, (p : ℂ) ^ (-(sR σ u)) = EdgeNonvanishing.ep p u ^ 2 * x := by
    intro u
    rw [← hX, EdgeNonvanishing.ep, sq, ← cpow_add _ _ hp0, ← cpow_add _ _ hp0]; congr 1; simp [sR]; ring
  have hR : ∀ s : ℂ, 1 < s.re → fR s p =
      ((1 - (p : ℂ) ^ (-s)) ^ 2 * (1 - α ^ 2 * (p : ℂ) ^ (-s)) * (1 - β ^ 2 * (p : ℂ) ^ (-s)))⁻¹ :=
    fun s hs' => rs_local hs' hp hab hs hα hβ
  have hR0 := hR σ (by simpa using hσ)
  have hR1 := hR (sR σ t) (by simp [sR]; linarith)
  have hR2 := hR (sR σ (-t)) (by simp [sR]; linarith)
  rw [hX] at hR0
  rw [hY t] at hR1
  rw [hY (-t)] at hR2
  have hLa := L_local (sL σ t) p hab hs
  have hLb := L_local (sL σ (-t)) p hab hs
  rw [hZ t] at hLa
  rw [hZ (-t)] at hLb
  obtain ⟨ℓ, hℓ0, hℓ⟩ := EdgeNonvanishing.localD_inv_eq_exp α β (EdgeNonvanishing.ep p t)
    (EdgeNonvanishing.ep p (-t)) (lam p) (2 * (EdgeNonvanishing.ep p t).re) x hx0 hab hs
    (EdgeNonvanishing.ep_mul hp t) (EdgeNonvanishing.ep_add_real t) hα1 hβ
    (EdgeNonvanishing.ep_norm hp t) (EdgeNonvanishing.ep_norm hp (-t)) hαx
  refine ⟨ℓ, hℓ0, ?_⟩
  rw [← hℓ, Fp, hX, hLa, hLb, hR0, hR1, hR2, EdgeNonvanishing.localD]
  simp only [mul_inv, ← inv_pow, ← mul_assoc]
  ring

/-- **Global positivity**: `‖F(σ)‖ ≥ 1` for every `σ > 1` and every `t`. -/
theorem one_le_norm_Fval {σ : ℝ} (hσ : 1 < σ) (t : ℝ) : 1 ≤ ‖Fval σ t‖ := by
  have hloc : ∀ p : Nat.Primes, ∃ ℓ : ℝ, 0 ≤ ℓ ∧ Fp σ t p = ((Real.exp ℓ : ℝ) : ℂ) :=
    fun p => Fp_eq_exp hσ t p.2
  choose ℓ hℓ0 hℓ using hloc
  have hN := (Fp_hasProd hσ t).norm
  have hpart : ∀ S : Finset Nat.Primes, 1 ≤ ∏ p ∈ S, ‖Fp σ t p‖ := by
    intro S
    have : ∏ p ∈ S, ‖Fp σ t p‖ = Real.exp (∑ p ∈ S, ℓ p) := by
      rw [Real.exp_sum]
      refine Finset.prod_congr rfl fun p _ => ?_
      rw [hℓ p, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    rw [this]
    exact Real.one_le_exp (Finset.sum_nonneg fun p _ => hℓ0 p)
  exact ge_of_tendsto' hN hpart

/-! ## The contradiction -/

/-- `ζ(2σ)R(σ) = O(1/(σ−1))`. -/
lemma rs_real_bound : ∃ C : ℝ, ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ),
    ‖riemannZeta (2 * ((1 + h : ℝ) : ℂ)) * RS ((1 + h : ℝ) : ℂ)‖ ≤ C / h := by
  obtain ⟨K, hK0, hK⟩ := rs_sub_zeta_bound
  have hz2 := EdgeNonvanishing.cont_bound (g := riemannZeta) (a := 2) (b := 2)
    (differentiableAt_riemannZeta (by norm_num)).continuousAt
  refine ⟨(‖riemannZeta 2‖ + 1) * (2 * |rsc| + 5 * K), ?_⟩
  filter_upwards [hz2, EdgeNonvanishing.zeta_bound, self_mem_nhdsWithin,
    Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with h h1 h2 (hpos : 0 < h) hh1
  have hh1' : h < 1 := hh1.2
  set s : ℂ := ((1 + h : ℝ) : ℂ)
  have hsre : s.re = 1 + h := by simp [s]
  have hsn : ‖s‖ = 1 + h := by
    simp only [s, Complex.norm_real, Real.norm_eq_abs]; rw [abs_of_pos (by linarith)]
  have hR := hK s (by rw [hsre]; linarith)
  have hzs : ‖riemannZeta s‖ ≤ 2 / h := by
    have : s = 1 + (h : ℂ) := by simp [s]
    rw [this]; exact h2
  have h2s : riemannZeta (2 * s) = riemannZeta (2 + 2 * (h : ℂ)) := by
    congr 1; simp [s]; ring
  have hRS : ‖RS s‖ ≤ (2 * |rsc| + 5 * K) / h := by
    have e1 : ‖RS s‖ ≤ ‖(rsc : ℂ) * riemannZeta s‖ + K * ‖s‖ / (s.re - 3 / 5) := by
      have := norm_le_norm_add_norm_sub' (RS s) ((rsc : ℂ) * riemannZeta s)
      linarith
    have e2 : ‖(rsc : ℂ) * riemannZeta s‖ ≤ |rsc| * (2 / h) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hzs (abs_nonneg _)
    have e3 : K * ‖s‖ / (s.re - 3 / 5) ≤ 5 * K / h := by
      rw [hsn, hsre, div_le_div_iff₀ (by linarith) hpos]
      nlinarith [mul_nonneg (mul_nonneg hK0 hpos.le) (sub_pos.mpr hh1').le, mul_nonneg hK0 hpos.le]
    calc ‖RS s‖ ≤ |rsc| * (2 / h) + 5 * K / h := by linarith
      _ = (2 * |rsc| + 5 * K) / h := by field_simp
  rw [norm_mul, h2s]
  calc ‖riemannZeta (2 + 2 * (h : ℂ))‖ * ‖RS s‖ ≤ (‖riemannZeta 2‖ + 1) * ((2 * |rsc| + 5 * K) / h) :=
        mul_le_mul h1 hRS (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- `ζ(2σ+4iu)R(σ+2iu) = O(1)` for `u ≠ 0`. -/
lemma rs_line_bound {u : ℝ} (hu : u ≠ 0) : ∃ C : ℝ, ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ),
    ‖riemannZeta (2 * sR (1 + h) u) * RS (sR (1 + h) u)‖ ≤ C := by
  obtain ⟨K, hK0, hK⟩ := rs_sub_zeta_bound
  set a : ℂ := 1 + 2 * (u : ℂ) * I
  have ha1 : a ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp [a] at this
    exact hu this
  have ha2 : 2 * a ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num [a] at this
  have hz1 := EdgeNonvanishing.cont_bound (g := riemannZeta) (a := a) (b := 1)
    (differentiableAt_riemannZeta ha1).continuousAt
  have hz2 := EdgeNonvanishing.cont_bound (g := riemannZeta) (a := 2 * a) (b := 2)
    (differentiableAt_riemannZeta ha2).continuousAt
  refine ⟨(‖riemannZeta (2 * a)‖ + 1) * (|rsc| * (‖riemannZeta a‖ + 1) + K * (‖a‖ + 1) * (5 / 2)), ?_⟩
  filter_upwards [hz1, hz2, self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)]
    with h h1 h2 (hpos : 0 < h) hh1
  have hh1' : h < 1 := hh1.2
  have hs : sR (1 + h) u = a + 1 * (h : ℂ) := by simp [sR, a]; ring
  have h2s : 2 * sR (1 + h) u = 2 * a + 2 * (h : ℂ) := by rw [hs]; ring
  rw [norm_mul, h2s, hs]
  set s := a + 1 * (h : ℂ)
  have hsre : s.re = 1 + h := by simp [s, a]
  have hsn : ‖s‖ ≤ ‖a‖ + 1 := by
    calc ‖s‖ ≤ ‖a‖ + ‖1 * (h : ℂ)‖ := norm_add_le _ _
      _ ≤ ‖a‖ + 1 := by
        rw [one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]; linarith
  have hR := hK s (by rw [hsre]; linarith)
  have hRS : ‖RS s‖ ≤ |rsc| * (‖riemannZeta a‖ + 1) + K * (‖a‖ + 1) * (5 / 2) := by
    have e1 : ‖RS s‖ ≤ ‖(rsc : ℂ) * riemannZeta s‖ + K * ‖s‖ / (s.re - 3 / 5) := by
      have := norm_le_norm_add_norm_sub' (RS s) ((rsc : ℂ) * riemannZeta s)
      linarith
    have e2 : ‖(rsc : ℂ) * riemannZeta s‖ ≤ |rsc| * (‖riemannZeta a‖ + 1) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    have e3 : K * ‖s‖ / (s.re - 3 / 5) ≤ K * (‖a‖ + 1) * (5 / 2) := by
      rw [hsre, div_le_iff₀ (by linarith)]
      have : K * ‖s‖ ≤ K * (‖a‖ + 1) := mul_le_mul_of_nonneg_left hsn hK0
      nlinarith [mul_nonneg (mul_nonneg hK0 (by positivity : (0 : ℝ) ≤ ‖a‖ + 1)) hpos.le]
    linarith
  exact mul_le_mul h2 hRS (norm_nonneg _) (by positivity)

lemma L_zero_conj {s : ℂ} (h : L s = 0) : L (conj s) = 0 := by
  rw [L_conj, h, map_zero]

/-- **Edge non-vanishing, `t ≠ 0`** (unconditional for `EData`). -/
theorem L_ne_zero_edge_of_ne {t : ℝ} (ht : t ≠ 0) : L (1 + t * I) ≠ 0 := by
  intro h0
  have h0' : L (1 + ((-t : ℝ) : ℂ) * I) = 0 := by
    have := L_zero_conj h0
    have e : conj ((1 : ℂ) + t * I) = 1 + ((-t : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp
    rwa [e] at this
  have hd := L_diff
  obtain ⟨Ca, hCa⟩ := EdgeNonvanishing.zero_bound (hd (1 + t * I)) h0
  obtain ⟨Cb, hCb⟩ := EdgeNonvanishing.zero_bound (hd (1 + ((-t : ℝ) : ℂ) * I)) h0'
  obtain ⟨C4, hC4⟩ := rs_real_bound
  obtain ⟨C5, hC5⟩ := rs_line_bound ht
  obtain ⟨C6, hC6⟩ := rs_line_bound (neg_ne_zero.mpr ht)
  set M : ℝ := 2 * |Ca| ^ 2 * |Cb| ^ 2 * |C4| ^ 2 * |C5| * |C6|
  have hM : 0 ≤ M := by positivity
  have hsmallE : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), x ∈ Set.Ioo 0 (1 / (M + 1)) :=
    Ioo_mem_nhdsGT (by positivity)
  have hposE : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), x ∈ Set.Ioi 0 := eventually_mem_nhdsWithin
  have hall := EdgeNonvanishing.zeta_bound.and
    (hCa.and (hCb.and (hC4.and (hC5.and (hC6.and (hposE.and hsmallE))))))
  obtain ⟨h, hh⟩ := hall.exists
  obtain ⟨hz, ha, hb, h4, h5, h6, hpos, hsmall⟩ := hh
  have hpos : 0 < h := hpos
  have hsm : h < 1 / (M + 1) := hsmall.2
  have hsL : ∀ u : ℝ, sL (1 + h) u = 1 + (u : ℂ) * I + h := fun u => by
    simp [sL]; ring
  have hF := one_le_norm_Fval (σ := 1 + h) (by linarith) t
  have e1 : ‖riemannZeta ((1 + h : ℝ) : ℂ)‖ ≤ 2 / h := by
    have : ((1 + h : ℝ) : ℂ) = 1 + (h : ℂ) := by push_cast; ring
    rw [this]; exact hz
  rw [Fval, hsL t, hsL (-t)] at hF
  simp only [norm_mul] at hF
  have h5' : ‖riemannZeta (2 * sR (1 + h) t)‖ * ‖RS (sR (1 + h) t)‖ ≤ |C5| := by
    rw [← norm_mul]; exact h5.trans (le_abs_self _)
  have h6' : ‖riemannZeta (2 * sR (1 + h) (-t))‖ * ‖RS (sR (1 + h) (-t))‖ ≤ |C6| := by
    rw [← norm_mul]; exact h6.trans (le_abs_self _)
  rw [norm_mul] at h4
  have ha' := ha.trans (mul_le_mul_of_nonneg_right (le_abs_self Ca) hpos.le)
  have hb' := hb.trans (mul_le_mul_of_nonneg_right (le_abs_self Cb) hpos.le)
  have h4' := h4.trans (div_le_div_of_nonneg_right (le_abs_self C4) hpos.le)
  have key : 1 ≤ (2 / h) * ((|Ca| * h) * (|Ca| * h)) * ((|Cb| * h) * (|Cb| * h)) *
      ((|C4| / h) * (|C4| / h)) * |C5| * |C6| := by
    refine hF.trans ?_
    gcongr
  have hval : (2 / h) * ((|Ca| * h) * (|Ca| * h)) * ((|Cb| * h) * (|Cb| * h)) *
      ((|C4| / h) * (|C4| / h)) * |C5| * |C6| = M * h := by
    simp only [M]; field_simp
  rw [hval] at key
  have : M * h < 1 := by
    rw [lt_div_iff₀ (by positivity)] at hsm
    nlinarith
  linarith

/-- **Non-vanishing on the closed half-plane `Re s ≥ 1`**, given the real edge point. -/
theorem L_ne_zero_of_ge (h1 : L 1 ≠ 0) {s : ℂ} (hs : 1 ≤ s.re) : L s ≠ 0 := by
  rcases hs.lt_or_eq with hs | hs
  · exact L_ne_zero_of_gt hs
  · have e : s = 1 + (s.im : ℂ) * I := by
      apply Complex.ext <;> simp [← hs]
    rcases eq_or_ne s.im 0 with h0 | h0
    · rw [e, h0]; simpa using h1
    · rw [e]; exact L_ne_zero_edge_of_ne h0

end RamanujanTau.EigenformEdge
