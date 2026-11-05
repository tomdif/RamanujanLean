/-
# The dual expansion, part A: the integrand and its holomorphic correction

For `RSDataM m a κ`, put (with `x > 0` fixed)

    Ψ(s) = x^s R_k(s) (s(s−1)Λ₀(s) + κ)                  (entire),
    Φ(s) = Ψ(s)/(s(s−1)),
    H(s) = Φ(s) − Ψ(1)(1/(s−1) − 1/(s+2)) + Ψ(0)(1/s − 1/(s+2)).

`H` is holomorphic on `Re s > −2` (two `dslope`s remove the poles at `0, 1`), and

* on `Re s > 2`, `s` not a pole of `P_k`: `x^s P_k(s) ζ(2s)D(s) = Φ(s)` (`Phi_eq_right`);
* on `Re s < −1`, `s ∉ −ℕ`: `Φ(s) = x^s Q_k(s) ζ(2−2s)D(1−s)` (`Phi_eq_left`), by `Λ₀(1−s) = Λ₀(s)`;
* `‖H(s)‖ ≤ C (1+|Im s|)^{−2}` on `−3/2 ≤ Re s ≤ 5/2` once `k ≥ 18` (`H_bound`), from the
  Phragmén–Lindelöf bound `RankinErrorGeneral.fPLM_bound`.
-/
import RamanujanTau.RankinLandau.KernelLine
import RamanujanTau.RankinLandau.Residue
import RamanujanTau.RankinErrorGeneral.PL

set_option autoImplicit false

namespace RamanujanTau.RankinLandau

open Complex Real MeasureTheory Set Filter Topology Finset
open RamanujanTau.RankinError RamanujanTau.RankinErrorGeneral

lemma prod_add_ne_zero {s : ℂ} (hs : ∀ j : ℕ, s + j ≠ 0) (k : ℕ) :
    ∏ j ∈ range (k + 1), (s + j) ≠ 0 :=
  prod_ne_zero_iff.2 fun j _ => hs j

lemma add_nat_ne_zero_of_im {s : ℂ} (hs : s.im ≠ 0) (j : ℕ) : s + j ≠ 0 := by
  intro h; have := congrArg Complex.im h; simp at this; exact hs this

lemma add_nat_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) (j : ℕ) : s + j ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp at this
  linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]

lemma add_nat_ne_zero_of_half {s : ℂ} (hs : s.re = -3 / 2) (j : ℕ) : s + j ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp [hs] at this
  have h2 : (2 * j : ℝ) = 3 := by linarith
  have h3 : (2 * j : ℕ) = 3 := by exact_mod_cast h2
  omega

/-- `P_k(s) γₘ(s)⁻¹ = R_k(s)` away from the poles of `P_k`. -/
lemma Pk_mul_invGamM (m k : ℕ) {s : ℂ} (hs : ∀ j : ℕ, s + j ≠ 0) :
    Pk k s * invGamM m s = Rk m k s := by
  have hP := prod_add_ne_zero hs k
  unfold Pk invGamM Rk
  rw [inv_Gamma_eq_prod s (k + 1)]
  rw [show s + ((k + 1 : ℕ) : ℂ) = s + k + 1 by push_cast; ring]
  field_simp

section Data

variable {m : ℕ} {a : ℕ → ℝ} {κ : ℝ} (d : RSDataM m a κ) (k : ℕ) (x : ℝ)

/-- `Ψ(s) = x^s R_k(s) (s(s−1)Λ₀(s) + κ)`. -/
noncomputable def Psi (s : ℂ) : ℂ := (x : ℂ) ^ s * Rk m k s * (s * (s - 1) * d.Λ₀ s + κ)

/-- `Φ(s) = Ψ(s)/(s(s−1))`. -/
noncomputable def Phi (s : ℂ) : ℂ := Psi d k x s / (s * (s - 1))

/-- The numerator `N(s) = Ψ(s)(s+2) − 3Ψ(1)s + 2Ψ(0)(s−1)`. -/
noncomputable def Nfun (s : ℂ) : ℂ :=
  Psi d k x s * (s + 2) - 3 * Psi d k x 1 * s + 2 * Psi d k x 0 * (s - 1)

/-- The holomorphic correction `H = N/(s(s−1)(s+2))`. -/
noncomputable def Hfun (s : ℂ) : ℂ := dslope (dslope (Nfun d k x) 0) 1 s / (s + 2)

/-- The two partial-fraction weights. -/
noncomputable def u1 (s : ℂ) : ℂ := 1 / (s - 1) - 1 / (s + 2)
noncomputable def u0 (s : ℂ) : ℂ := 1 / s - 1 / (s + 2)

variable (hx : 0 < x)
include hx

lemma differentiable_Psi : Differentiable ℂ (Psi d k x) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  intro s
  unfold Psi
  exact ((differentiableAt_id.const_cpow (Or.inl hx0)).mul (differentiable_Rk m k s)).mul
    (((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul (d.diff s)).add_const _)

lemma differentiable_Nfun : Differentiable ℂ (Nfun d k x) := by
  have := differentiable_Psi d k x hx
  intro s; unfold Nfun
  fun_prop

lemma Nfun_zero : Nfun d k x 0 = 0 := by unfold Nfun; ring
lemma Nfun_one : Nfun d k x 1 = 0 := by unfold Nfun; ring

lemma differentiableOn_Hfun : DifferentiableOn ℂ (Hfun d k x) {s : ℂ | -2 < s.re} := by
  have hN := differentiable_Nfun d k x hx
  have h1 : Differentiable ℂ (dslope (Nfun d k x) 0) := by
    rw [← differentiableOn_univ, differentiableOn_dslope (by simp)]
    exact hN.differentiableOn
  have h2 : Differentiable ℂ (dslope (dslope (Nfun d k x) 0) 1) := by
    rw [← differentiableOn_univ, differentiableOn_dslope (by simp)]
    exact h1.differentiableOn
  intro s hs
  simp only [mem_setOf_eq] at hs
  have hs2 : s + 2 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  exact ((h2 s).div (differentiableAt_id.add_const 2) hs2).differentiableWithinAt

/-- Off `{0, 1, −2}`, `H = Φ − Ψ(1) u₁ + Ψ(0) u₀`. -/
lemma Hfun_eq {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) (h2 : s + 2 ≠ 0) :
    Hfun d k x s = Phi d k x s - Psi d k x 1 * u1 s + Psi d k x 0 * u0 s := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.2 h1
  unfold Hfun Phi u1 u0
  rw [dslope_of_ne _ h1, slope_def_field, dslope_of_ne _ h0, slope_def_field,
    dslope_of_ne _ (one_ne_zero), slope_def_field, Nfun_zero d k x hx, Nfun_one d k x hx]
  unfold Nfun
  simp only [sub_zero]
  field_simp
  ring

omit hx in
/-- On `Re s > 2`: `x^s P_k(s) ζ(2s) D(s) = Φ(s)`. -/
lemma Phi_eq_right {s : ℂ} (hs : 2 < s.re) :
    (x : ℂ) ^ s * Pk k s * (riemannZeta (2 * s) * LSeries (fun n => (a n : ℂ)) s) =
      Phi d k x s := by
  have h0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  have h1 : s - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hu := d.unfold s hs
  have hgi := gamM_mul_invGamM m (s := s) (by linarith)
  have hz : riemannZeta (2 * s) * LSeries (fun n => (a n : ℂ)) s =
      invGamM m s * (d.Λ₀ s + κ * (1 / (s - 1) - 1 / s)) := by
    rw [← hu]
    linear_combination (-(riemannZeta (2 * s) * LSeries (fun n => (a n : ℂ)) s)) * hgi
  have hj : ∀ j : ℕ, s + j ≠ 0 := add_nat_ne_zero_of_re_pos (by linarith)
  unfold Phi Psi
  rw [hz, ← Pk_mul_invGamM m k hj]
  field_simp
  ring

omit hx in
/-- On `Re s < −1`, away from `−ℕ`: `Φ(s) = x^s Q_k(s) ζ(2−2s) D(1−s)`. -/
lemma Phi_eq_left {s : ℂ} (hs : s.re < -1) :
    Phi d k x s = (x : ℂ) ^ s * Qk m k s *
      (riemannZeta (2 * (1 - s)) * LSeries (fun n => (a n : ℂ)) (1 - s)) := by
  have h0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  have h1 : s - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hu := d.unfold (1 - s) (by simp; linarith)
  rw [d.fe s] at hu
  have hw : 1 - s - 1 = -s := by ring
  rw [hw] at hu
  unfold Phi Psi Qk
  rw [show (x : ℂ) ^ s * (Rk m k s * gamM m (1 - s)) *
      (riemannZeta (2 * (1 - s)) * LSeries (fun n => (a n : ℂ)) (1 - s)) =
      (x : ℂ) ^ s * Rk m k s * (gamM m (1 - s) * riemannZeta (2 * (1 - s)) *
        LSeries (fun n => (a n : ℂ)) (1 - s)) by ring, hu]
  have h1' : (1 : ℂ) - s ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  field_simp
  ring

omit hx in
lemma norm_Pk_le_im (k : ℕ) {s : ℂ} (hs : s.im ≠ 0) :
    ‖Pk k s‖ ≤ (k.factorial : ℝ) / |s.im| ^ (k + 1) := by
  unfold Pk
  rw [norm_div, Complex.norm_natCast, norm_prod]
  have hpos : 0 < |s.im| := abs_pos.2 hs
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  calc |s.im| ^ (k + 1) = ∏ _j ∈ range (k + 1), |s.im| := by rw [prod_const, card_range]
    _ ≤ ∏ j ∈ range (k + 1), ‖s + j‖ := by
        refine prod_le_prod (fun _ _ => abs_nonneg _) (fun j _ => ?_)
        have := Complex.abs_im_le_norm (s + j); simpa using this

/-- **The strip bound for `H`** (needs `k ≥ 18`). -/
theorem H_bound (hx1 : 1 ≤ x) (hk : 18 ≤ k) (hm : 2 ≤ m)
    (hsum : LSeriesSummable (fun n => (a n : ℂ)) ((5 / 2 : ℝ) : ℂ)) :
    ∃ C : ℝ, ∀ s : ℂ, -3 / 2 ≤ s.re → s.re ≤ 5 / 2 →
      ‖Hfun d k x s‖ ≤ C * (1 + |s.im|) ^ (-(2 : ℝ)) := by
  obtain ⟨CP, hCP⟩ := fPLM_bound d hsum hm
  have hKc : IsCompact (Icc (-3 / 2 : ℝ) (5 / 2) ×ℂ Icc (-1 : ℝ) 1) :=
    isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn
    ((differentiableOn_Hfun d k x hx).continuousOn.mono (fun s hs => by
      rw [mem_reProdIm] at hs; simp only [mem_setOf_eq]; linarith [hs.1.1]))
  set A₁ : ℝ := x ^ (5 / 2 : ℝ) * (k.factorial : ℝ) * 6 ^ 19 * |CP| * 2 ^ (k + 3) with hA₁
  set C : ℝ := A₁ + 12 * ‖Psi d k x 1‖ + 8 * ‖Psi d k x 0‖ + 4 * |B| with hC
  have hA₁0 : 0 ≤ A₁ := by positivity
  refine ⟨C, fun s h1 h2 => ?_⟩
  set t : ℝ := s.im with ht
  have ht0 : (0 : ℝ) < 1 + |t| := by positivity
  rw [Real.rpow_neg ht0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hT2 : 0 < (1 + |t|) ^ 2 := by positivity
  rcases le_or_gt |t| 1 with htl | htl
  · -- compact part
    have := hB s (by rw [mem_reProdIm]; exact ⟨⟨h1, h2⟩, abs_le.1 htl⟩)
    have h4 : (1 + |t|) ^ 2 ≤ 4 := by nlinarith [abs_nonneg t]
    calc ‖Hfun d k x s‖ ≤ |B| := this.trans (le_abs_self B)
      _ = 4 * |B| * (4 : ℝ)⁻¹ := by ring
      _ ≤ 4 * |B| * ((1 + |t|) ^ 2)⁻¹ := by gcongr
      _ ≤ C * ((1 + |t|) ^ 2)⁻¹ := by
          gcongr
          rw [hC]; nlinarith [norm_nonneg (Psi d k x 1), norm_nonneg (Psi d k x 0)]
  · -- `|t| > 1`
    have hti : s.im ≠ 0 := by
      intro h; have h' : t = 0 := by rw [ht, h]
      rw [h'] at htl; simp at htl; linarith
    have hta : 0 < |t| := by linarith
    have hs0 : s ≠ 0 := by intro h; apply hti; rw [h]; simp
    have hs1 : s ≠ 1 := by intro h; apply hti; rw [h]; simp
    have hs2 : s + 2 ≠ 0 := by
      intro h; apply hti; have := congrArg Complex.im h; simpa using this
    have hs3 : s + 3 ≠ 0 := by
      intro h; apply hti; have := congrArg Complex.im h; simpa using this
    have hj : ∀ j : ℕ, s + j ≠ 0 := add_nat_ne_zero_of_im hti
    rw [Hfun_eq d k x hx hs0 hs1 hs2]
    have hhalf : (1 + |t|) / 2 ≤ |t| := by linarith
    have hnorm_im : ∀ z : ℂ, z.im = t → |t| ≤ ‖z‖ := fun z hz => by
      have := Complex.abs_im_le_norm z; rwa [hz] at this
    -- `Φ`
    have hPsi : Psi d k x s = (x : ℂ) ^ s * Pk k s * (s + 3) ^ 19 * fPLM d s := by
      unfold Psi fPLM
      rw [← Pk_mul_invGamM m k hj]
      field_simp
    have hPhi : ‖Phi d k x s‖ ≤ A₁ * ((1 + |t|) ^ 2)⁻¹ := by
      unfold Phi
      rw [hPsi, norm_div, norm_mul, norm_mul, norm_mul, norm_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos hx, norm_pow]
      have hxs : x ^ s.re ≤ x ^ (5 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 h2
      have hP := norm_Pk_le_im k hti
      rw [← ht] at hP
      have h3 : ‖s + 3‖ ≤ 6 * (1 + |t|) := by
        have hre0 : (s + 3).re = s.re + 3 := by simp
        have hre : |(s + 3).re| ≤ 11 / 2 := by
          rw [hre0, abs_le]; constructor <;> linarith
        have him : |(s + 3).im| = |t| := by simp [ht]
        calc ‖s + 3‖ ≤ |(s + 3).re| + |(s + 3).im| := Complex.norm_le_abs_re_add_abs_im _
          _ ≤ 11 / 2 + |t| := by rw [him]; linarith
          _ ≤ 6 * (1 + |t|) := by nlinarith [abs_nonneg t]
      have hss : |t| ^ 2 ≤ ‖s‖ * ‖s - 1‖ := by
        rw [sq]
        exact mul_le_mul (hnorm_im s rfl) (hnorm_im (s - 1) (by simp [ht])) hta.le (norm_nonneg _)
      have hF := hCP s h1 h2
      have hden : 0 < ‖s‖ * ‖s - 1‖ := lt_of_lt_of_le (by positivity) hss
      rw [div_le_iff₀ hden]
      have hpow : (1 + |t|) ^ 19 * (1 + |t|) ^ 2 ≤ (1 + |t|) ^ (k + 3) := by
        rw [← pow_add]; exact pow_le_pow_right₀ (by linarith [abs_nonneg t]) (by omega)
      have htk : ((1 + |t|) / 2) ^ (k + 3) ≤ |t| ^ (k + 3) := pow_le_pow_left₀ (by positivity) hhalf _
      have htk' : |t| ^ (k + 1) * |t| ^ 2 = |t| ^ (k + 3) := by rw [← pow_add]
      calc x ^ s.re * ‖Pk k s‖ * ‖s + 3‖ ^ 19 * ‖fPLM d s‖
          ≤ x ^ (5 / 2 : ℝ) * ((k.factorial : ℝ) / |t| ^ (k + 1)) * (6 * (1 + |t|)) ^ 19 * |CP| := by
            gcongr
            exact hF.trans (le_abs_self _)
        _ = x ^ (5 / 2 : ℝ) * (k.factorial : ℝ) * 6 ^ 19 * |CP| * (1 + |t|) ^ 19 / |t| ^ (k + 1) := by
            rw [mul_pow]; ring
        _ ≤ A₁ * ((1 + |t|) ^ 2)⁻¹ * (‖s‖ * ‖s - 1‖) := by
            rw [div_le_iff₀ (by positivity)]
            have key : x ^ (5 / 2 : ℝ) * (k.factorial : ℝ) * 6 ^ 19 * |CP| * (1 + |t|) ^ 19 ≤
                A₁ * ((1 + |t|) ^ 2)⁻¹ * (|t| ^ 2 * |t| ^ (k + 1)) := by
              rw [mul_comm (|t| ^ 2), htk', hA₁]
              have e2 : ((1 + |t|) / 2) ^ (k + 3) * 2 ^ (k + 3) = (1 + |t|) ^ (k + 3) := by
                rw [← mul_pow]; ring_nf
              have hq : (1 + |t|) ^ 19 ≤ ((1 + |t|) ^ 2)⁻¹ * (|t| ^ (k + 3) * 2 ^ (k + 3)) := by
                rw [le_inv_mul_iff₀ hT2]
                calc (1 + |t|) ^ 2 * (1 + |t|) ^ 19 ≤ (1 + |t|) ^ (k + 3) := by
                      rw [mul_comm]; exact hpow
                  _ = ((1 + |t|) / 2) ^ (k + 3) * 2 ^ (k + 3) := e2.symm
                  _ ≤ |t| ^ (k + 3) * 2 ^ (k + 3) := by gcongr
              have h00 : 0 ≤ x ^ (5 / 2 : ℝ) * (k.factorial : ℝ) * 6 ^ 19 * |CP| := by positivity
              calc x ^ (5 / 2 : ℝ) * (k.factorial : ℝ) * 6 ^ 19 * |CP| * (1 + |t|) ^ 19
                  ≤ x ^ (5 / 2 : ℝ) * (k.factorial : ℝ) * 6 ^ 19 * |CP| *
                    (((1 + |t|) ^ 2)⁻¹ * (|t| ^ (k + 3) * 2 ^ (k + 3))) := by gcongr
                _ = _ := by ring
            calc x ^ (5 / 2 : ℝ) * (k.factorial : ℝ) * 6 ^ 19 * |CP| * (1 + |t|) ^ 19 ≤
                A₁ * ((1 + |t|) ^ 2)⁻¹ * (|t| ^ 2 * |t| ^ (k + 1)) := key
              _ ≤ A₁ * ((1 + |t|) ^ 2)⁻¹ * (‖s‖ * ‖s - 1‖) * |t| ^ (k + 1) := by
                  rw [← mul_assoc]; gcongr
    -- `u₁, u₀`
    have hu1 : ‖u1 s‖ ≤ 12 * ((1 + |t|) ^ 2)⁻¹ := by
      have e : u1 s = 3 / ((s - 1) * (s + 2)) := by
        unfold u1; have : s - 1 ≠ 0 := sub_ne_zero.2 hs1; field_simp; ring
      rw [e, norm_div, norm_mul, show ‖(3 : ℂ)‖ = 3 by simp]
      have ha := hnorm_im (s - 1) (by simp [ht])
      have hb := hnorm_im (s + 2) (by simp [ht])
      rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) (mul_le_mul ha hb hta.le (norm_nonneg _)))]
      have : ((1 + |t|) / 2) ^ 2 ≤ ‖s - 1‖ * ‖s + 2‖ := by
        rw [sq]; exact mul_le_mul (hhalf.trans ha) (hhalf.trans hb) (by positivity) (norm_nonneg _)
      calc (3 : ℝ) = 12 * ((1 + |t|) ^ 2)⁻¹ * ((1 + |t|) / 2) ^ 2 := by field_simp; ring
        _ ≤ 12 * ((1 + |t|) ^ 2)⁻¹ * (‖s - 1‖ * ‖s + 2‖) := by gcongr
    have hu0 : ‖u0 s‖ ≤ 8 * ((1 + |t|) ^ 2)⁻¹ := by
      have e : u0 s = 2 / (s * (s + 2)) := by unfold u0; field_simp; ring
      rw [e, norm_div, norm_mul, show ‖(2 : ℂ)‖ = 2 by simp]
      have ha := hnorm_im s rfl
      have hb := hnorm_im (s + 2) (by simp [ht])
      rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) (mul_le_mul ha hb hta.le (norm_nonneg _)))]
      have : ((1 + |t|) / 2) ^ 2 ≤ ‖s‖ * ‖s + 2‖ := by
        rw [sq]; exact mul_le_mul (hhalf.trans ha) (hhalf.trans hb) (by positivity) (norm_nonneg _)
      calc (2 : ℝ) = 8 * ((1 + |t|) ^ 2)⁻¹ * ((1 + |t|) / 2) ^ 2 := by field_simp; ring
        _ ≤ 8 * ((1 + |t|) ^ 2)⁻¹ * (‖s‖ * ‖s + 2‖) := by gcongr
    calc ‖Phi d k x s - Psi d k x 1 * u1 s + Psi d k x 0 * u0 s‖
        ≤ ‖Phi d k x s - Psi d k x 1 * u1 s‖ + ‖Psi d k x 0 * u0 s‖ := norm_add_le _ _
      _ ≤ ‖Phi d k x s‖ + ‖Psi d k x 1 * u1 s‖ + ‖Psi d k x 0 * u0 s‖ := by
          gcongr; exact norm_sub_le _ _
      _ = ‖Phi d k x s‖ + ‖Psi d k x 1‖ * ‖u1 s‖ + ‖Psi d k x 0‖ * ‖u0 s‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ A₁ * ((1 + |t|) ^ 2)⁻¹ + ‖Psi d k x 1‖ * (12 * ((1 + |t|) ^ 2)⁻¹) +
          ‖Psi d k x 0‖ * (8 * ((1 + |t|) ^ 2)⁻¹) := by gcongr
      _ = (A₁ + 12 * ‖Psi d k x 1‖ + 8 * ‖Psi d k x 0‖) * ((1 + |t|) ^ 2)⁻¹ := by ring
      _ ≤ C * ((1 + |t|) ^ 2)⁻¹ := by
          gcongr; rw [hC]; linarith [abs_nonneg B]

end Data

end RamanujanTau.RankinLandau

#print axioms RamanujanTau.RankinLandau.Phi_eq_right
#print axioms RamanujanTau.RankinLandau.Phi_eq_left
#print axioms RamanujanTau.RankinLandau.H_bound
