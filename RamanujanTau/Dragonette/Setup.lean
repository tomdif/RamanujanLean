/-
# The circle method for `f(q)` at `q = −1`: setup

* `α n = [qⁿ] f(q)` (`MockTheta3.f3`), `|α n| ≤ p(n)`, and `f(−e^{−z}) = Σ (−1)^k α(k) e^{−kz}`;
* the coefficient integral `2π(−1)ⁿ α(n) = ∫_{−π}^{π} f(−e^{−z}) e^{nz} dθ`, `z = t + iθ`;
* the saddle point `t = π/√(24n)`, `A = nt = π²/(24t)` (so `2A = π√(n/6)`);
* the pointwise decomposition `f(−e^{−z}) e^{nz} = 2φ(e^{−z}) e^{nz} − M(θ)·Fr(z) Jt(π²/z)` with the main
  integrand `M(θ) = (z/π)^{−1/2} e^{π²/(24z) − z/24} e^{nz}` (Watson's `f + b = 2φ(−q)` and the transformation of `b`).
-/
import RamanujanTau.Dragonette.Estimates
import RamanujanTau.Dragonette.Laplace

set_option autoImplicit false

namespace Dragonette
open Complex Filter Metric MeasureTheory intervalIntegral HardyRamanujan
open scoped Real Topology

/-- the coefficients of `f(q)`: `α(n) = N(0,2,n) − N(1,2,n)`. -/
noncomputable abbrev α (n : ℕ) : ℤ := PowerSeries.coeff n MockTheta3.f3

lemma coeff_T_fA (k : ℕ) : PowerSeries.coeff k (Taylor.T MockTheta3.Radial.fA) = (α k : ℂ) := by
  rw [MockTheta3.Radial.fA_T.2, show MockTheta5.JTP.ψC = PowerSeries.map (Int.castRingHom ℂ) from rfl,
    PowerSeries.coeff_map]
  simp only [eq_intCast]
  congr 2
  unfold MockTheta3.f3
  congr 1; funext m; congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [MockTheta3.Radial.P1, MockTheta3.Radial.coe_prod_one_add (fun i => i + 1), MockTheta3.negPoch]
  simp

lemma abs_α_le (k : ℕ) : |(α k : ℝ)| ≤ p k := by
  unfold α
  rw [MockTheta3.f3_rank]
  have h := Finset.filter_card_add_filter_neg_card_eq_card (s := Finset.univ)
    (fun l : k.Partition => Even (CrankProof.rank l))
  have hp : (p k : ℝ) = ((Finset.univ.filter fun l : k.Partition => Even (CrankProof.rank l)).card : ℝ) +
      ((Finset.univ.filter fun l : k.Partition => ¬ Even (CrankProof.rank l)).card : ℝ) := by
    rw [p]; exact_mod_cast (by rw [h]; rfl)
  push_cast
  rw [hp, abs_le]
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) ((Finset.univ.filter fun l : k.Partition =>
    Even (CrankProof.rank l)).card), Nat.cast_nonneg (α := ℝ) ((Finset.univ.filter fun l : k.Partition =>
    ¬ Even (CrankProof.rank l)).card)]

lemma neg_mem_ball {s : ℂ} (hs : s ∈ ball (0 : ℂ) 1) : -s ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, norm_neg]; exact mem_ball_zero_iff.mp hs

lemma hasSum_fA {s : ℂ} (hs : s ∈ ball (0 : ℂ) 1) :
    HasSum (fun k => ((-1) ^ k * (α k : ℂ)) * s ^ k) (MockTheta3.Radial.fA (-s)) := by
  have h := MockTheta3.Radial.fA_T.1.hasSum (neg_mem_ball hs)
  simp only [coeff_T_fA] at h
  convert h using 2 with k
  rw [neg_pow]; ring

/-- **the coefficient integral**. -/
theorem coeff_integral_f (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (2 * π : ℂ) * ((-1) ^ n * (α n : ℂ)) =
      ∫ θ in (-π)..π, MockTheta3.Radial.fA (-cexp (-zt t θ)) * cexp (n * zt t θ) := by
  have hab : ∀ k, ‖(-1) ^ k * (α k : ℂ)‖ ≤ p k := fun k => by
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]; exact abs_α_le k
  let f : ℕ → C(ℝ, ℂ) := fun k => ⟨fun θ => (-1) ^ k * (α k : ℂ) * cexp ((n - k : ℤ) * zt t θ), by fun_prop⟩
  have hb : ∀ k, ‖(f k).restrict (⟨Set.uIcc (-π) π, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖
      ≤ (p k : ℝ) * Real.exp (-(k * t)) * Real.exp (n * t) := by
    intro k
    refine (ContinuousMap.norm_le _ (by positivity)).mpr fun θ => ?_
    simp only [ContinuousMap.restrict_apply, ContinuousMap.coe_mk, f]
    rw [norm_mul _ (cexp _), norm_exp, mul_assoc (p k : ℝ), ← Real.exp_add]
    gcongr
    · exact hab k
    · refine le_of_eq ?_; simp [zt]; ring
  have hsum : Summable fun k => ‖(f k).restrict (⟨Set.uIcc (-π) π, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb ((summable_p_exp ht).mul_right _)
  have H := hasSum_intervalIntegral_of_summable_norm hsum
  have hpt : ∀ θ : ℝ, ∑' k, f k θ = MockTheta3.Radial.fA (-cexp (-zt t θ)) * cexp (n * zt t θ) := by
    intro θ
    have hq : cexp (-zt t θ) ∈ ball (0 : ℂ) 1 := norm_cexp_neg_lt_one (by simp [zt]; exact ht)
    have h := (hasSum_fA hq).mul_right (cexp (n * zt t θ))
    rw [← h.tsum_eq]
    congr 1; funext k
    simp only [f, ContinuousMap.coe_mk]
    rw [show cexp (-zt t θ) ^ k = cexp (k * (-zt t θ)) from (Complex.exp_nat_mul _ k).symm,
      mul_assoc _ (cexp _) (cexp _), ← Complex.exp_add]
    congr 2; push_cast; ring
  simp only [hpt] at H
  rw [← H.tsum_eq]
  have hk : ∀ k, ∫ θ in (-π)..π, f k θ = if k = n then (2 * π : ℂ) * ((-1) ^ n * (α n : ℂ)) else 0 := by
    intro k
    simp only [f, ContinuousMap.coe_mk]
    have e : ∀ θ : ℝ, (-1) ^ k * (α k : ℂ) * cexp ((n - k : ℤ) * zt t θ) =
        ((-1) ^ k * (α k : ℂ) * cexp ((n - k : ℤ) * (t : ℂ))) * cexp ((n - k : ℤ) * (θ * I)) := by
      intro θ; rw [mul_assoc _ (cexp _) (cexp _), ← Complex.exp_add]; congr 2; simp [zt]; ring
    simp only [e, intervalIntegral.integral_const_mul, integral_exp_int]
    split_ifs with h1 h2 h2
    · subst h2; simp; ring
    · exact absurd (by omega) h2
    · exact absurd (by subst h2; simp) h1
    · simp
  simp only [hk]
  rw [tsum_ite_eq]

/-! ### the saddle point -/

noncomputable def tD (n : ℕ) : ℝ := π / √(24 * n)
noncomputable def AD (n : ℕ) : ℝ := n * tD n

lemma tD_pos {n : ℕ} (hn : 1 ≤ n) : 0 < tD n := by
  unfold tD; have : (0 : ℝ) < 24 * n := by positivity
  exact div_pos Real.pi_pos (Real.sqrt_pos.mpr this)

lemma AD_pos {n : ℕ} (hn : 1 ≤ n) : 0 < AD n := by unfold AD; have := tD_pos hn; positivity

lemma AD_eq {n : ℕ} (hn : 1 ≤ n) : π ^ 2 / (24 * tD n) = AD n := by
  have ht := tD_pos hn
  have h24 : (0 : ℝ) < 24 * n := by positivity
  have hs : √(24 * n) ^ 2 = 24 * n := Real.sq_sqrt h24.le
  unfold AD
  rw [div_eq_iff (by positivity)]
  unfold tD
  field_simp
  rw [mul_comm (n : ℝ) 24, hs]

lemma two_AD {n : ℕ} (hn : 1 ≤ n) : 2 * AD n = π * √(n / 6) := by
  have h24 : (0 : ℝ) < 24 * n := by positivity
  unfold AD tD
  have hs : √(24 * n) = 12 * √(n / 6) := by
    rw [show (24 : ℝ) * n = 12 ^ 2 * (n / 6) by ring, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have hpos : 0 < √((n : ℝ) / 6) := Real.sqrt_pos.mpr (by positivity)
  have hsq : √((n : ℝ) / 6) ^ 2 = n / 6 := Real.sq_sqrt (by positivity)
  rw [hs]
  field_simp
  nlinarith [hsq]

lemma tD_inv {n : ℕ} (hn : 1 ≤ n) : √(n : ℝ) ≤ π * (1 / tD n) := by
  unfold tD
  rw [one_div_div, mul_div_assoc', mul_comm π, mul_div_assoc, div_self Real.pi_ne_zero, mul_one]
  exact Real.sqrt_le_sqrt (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])

/-- **the main integrand** `M(θ) = (z/π)^{−1/2} e^{π²/(24z) − z/24} e^{nz}`. -/
noncomputable def MD (n : ℕ) (t θ : ℝ) : ℂ :=
  cexp (-(log (zt t θ / π) / 2)) * cexp (π ^ 2 / (24 * zt t θ) - zt t θ / 24) * cexp (n * zt t θ)

lemma zt_div_pi_ne {t θ : ℝ} (ht : 0 < t) : zt t θ / π ≠ 0 :=
  div_ne_zero (zt_ne_zero ht) (by exact_mod_cast Real.pi_ne_zero)

lemma re_zt_pos {t θ : ℝ} (ht : 0 < t) : 0 < (zt t θ).re := by simp [zt]; exact ht

/-- **the pointwise decomposition**. -/
theorem integrand_eq (n : ℕ) {t : ℝ} (ht : 0 < t) (θ : ℝ) :
    MockTheta3.Radial.fA (-cexp (-zt t θ)) * cexp (n * zt t θ) =
      2 * MockTheta3.Radial.gA (-cexp (-zt t θ)) * cexp (n * zt t θ) -
        MD n t θ * (Fr (zt t θ) * Jt (π ^ 2 / zt t θ)) := by
  set z := zt t θ
  have hz := re_zt_pos (θ := θ) ht
  have hb : -cexp (-z) ∈ ball (0 : ℂ) 1 := neg_mem_ball (norm_cexp_neg_lt_one hz)
  have hW := MockTheta3.Radial.watson_disc hb
  have hf : MockTheta3.Radial.fA (-cexp (-z)) =
      2 * MockTheta3.Radial.gA (-cexp (-z)) - MockTheta3.Radial.bA (-cexp (-z)) := by
    linear_combination hW
  have hJ := Jt_transform hz
  rw [cpow_def_of_ne_zero (zt_div_pi_ne ht)] at hJ
  have hJ' : Jt z = cexp (-(log (z / π) / 2)) * Jt (π ^ 2 / z) := by
    rw [hJ, ← mul_assoc, ← Complex.exp_add]
    rw [show -(log (z / π) / 2) + log (z / π) * (1 / 2) = 0 by ring, Complex.exp_zero, one_mul]
  rw [hf, bA_neg hz, Oz_transform hz, hJ', MD]
  ring

/-! ### the parametrization of the major arc -/

lemma log_scale {t : ℝ} (ht : 0 < t) (u : ℝ) :
    cexp (-(log ((t : ℂ) * (1 + u * I) / π) / 2)) = ((√(π / t) : ℝ) : ℂ) * cexp (-(log (1 + u * I) / 2)) := by
  have htπ : 0 < t / π := by positivity
  rw [show (t : ℂ) * (1 + u * I) / π = ((t / π : ℝ) : ℂ) * (1 + u * I) by push_cast; ring,
    Complex.log_ofReal_mul htπ (one_add_ne_zero u), add_div, neg_add, Complex.exp_add]
  congr 1
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity), Complex.ofReal_exp,
    show π / t = (t / π)⁻¹ by field_simp, Real.log_inv]
  push_cast; ring_nf

lemma MD_scale {n : ℕ} (hn : 1 ≤ n) (v : ℝ) :
    MD n (tD n) (tD n / √(AD n) * v) =
      ((√(π / tD n)) : ℂ) * ((Real.exp (2 * AD n) : ℝ) : ℂ) * hneg (v / √(AD n)) (tD n) v := by
  have ht := tD_pos hn
  have hA := AD_pos hn
  have hsA : 0 < √(AD n) := Real.sqrt_pos.mpr hA
  set t := tD n with htdef
  set A := AD n with hAdef
  set u := v / √A with hu
  have hz : zt t (t / √A * v) = (t : ℂ) * (1 + u * I) := by
    simp only [zt, hu]; push_cast; field_simp
  have hAt : (A : ℂ) = n * t := by rw [hAdef, AD]; push_cast; ring
  have hAπ : (π : ℂ) ^ 2 / (24 * t) = A := by
    have := AD_eq hn; rw [← htdef, ← hAdef] at this; exact_mod_cast this
  have hu2 : (A : ℂ) * (u : ℂ) ^ 2 = (v : ℂ) ^ 2 := by
    rw [hu]; push_cast
    have : (√A : ℂ) ^ 2 = A := by exact_mod_cast Real.sq_sqrt hA.le
    have hA0 : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
    field_simp
    rw [this]
    field_simp
  have hw := one_add_ne_zero u
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hexp : π ^ 2 / (24 * zt t (t / √A * v)) - zt t (t / √A * v) / 24 + n * zt t (t / √A * v) =
      2 * A + (-((t : ℂ) * (1 + u * I)) / 24) + (-((v : ℂ) ^ 2 / (1 + u * I))) := by
    rw [hz, ← hu2]
    have h1 : (π : ℂ) ^ 2 / (24 * (t * (1 + u * I))) = A / (1 + u * I) := by
      rw [← hAπ]; field_simp
    rw [h1, hAt]
    field_simp
    ring_nf
    rw [I_sq]
    ring
  unfold MD
  rw [mul_assoc, ← Complex.exp_add, hexp, hz, log_scale ht, Complex.exp_add, Complex.exp_add, ofReal_exp]
  unfold hneg
  push_cast
  ring

/-- the main-arc integral. -/
lemma major_main_D {n : ℕ} (hn : 1 ≤ n) :
    ∫ θ in (-tD n)..tD n, MD n (tD n) θ = ((tD n / √(AD n) * √(π / tD n) * Real.exp (2 * AD n) : ℝ) : ℂ) *
      ∫ v in (-√(AD n))..√(AD n), hneg (v / √(AD n)) (tD n) v := by
  have ht := tD_pos hn
  have hA := AD_pos hn
  have hsA : 0 < √(AD n) := Real.sqrt_pos.mpr hA
  set c : ℝ := tD n / √(AD n) with hc
  have hc0 : c ≠ 0 := by rw [hc]; positivity
  have hsub := intervalIntegral.integral_comp_mul_left (fun θ => MD n (tD n) θ) hc0
    (a := -√(AD n)) (b := √(AD n))
  have hcA : c * √(AD n) = tD n := by rw [hc]; field_simp
  rw [mul_neg, hcA] at hsub
  have : ∫ θ in (-tD n)..tD n, MD n (tD n) θ = c • ∫ v in (-√(AD n))..√(AD n), MD n (tD n) (c * v) := by
    rw [hsub, smul_smul, mul_inv_cancel₀ hc0, one_smul]
  rw [this]
  simp only [hc, MD_scale hn]
  rw [intervalIntegral.integral_const_mul, Complex.real_smul]
  push_cast; ring

/-- the normalization `K_n = 2√n e^{−2A}`. -/
noncomputable def KD (n : ℕ) : ℝ := 2 * √(n : ℝ) / Real.exp (2 * AD n)

lemma PD_eq {n : ℕ} (hn : 1 ≤ n) :
    KD n / (2 * π) * (tD n / √(AD n) * √(π / tD n) * Real.exp (2 * AD n)) = 1 / √π := by
  have ht := tD_pos hn
  have hA := AD_pos hn
  have hπ := Real.pi_pos
  have hnn : (0 : ℝ) < n := by exact_mod_cast hn
  set P := KD n / (2 * π) * (tD n / √(AD n) * √(π / tD n) * Real.exp (2 * AD n))
  have hP : 0 < P := by unfold P KD; positivity
  have hsq : P ^ 2 = 1 / π := by
    have hP' : P = √(n : ℝ) / π * (tD n / √(AD n) * √(π / tD n)) := by
      unfold P KD; field_simp
    rw [hP', mul_pow, mul_pow, div_pow, div_pow, Real.sq_sqrt hnn.le, Real.sq_sqrt hA.le,
      Real.sq_sqrt (by positivity)]
    unfold AD
    field_simp
  have h2 : (1 / √π) ^ 2 = 1 / π := by rw [div_pow, Real.sq_sqrt hπ.le, one_pow]
  have h1 : 0 < 1 / √π := by positivity
  nlinarith [sq_nonneg (P - 1 / √π), sq_nonneg (P + 1 / √π)]

end Dragonette
