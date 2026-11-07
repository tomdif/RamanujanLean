import RamanujanTau.TheoremA.EtaCuspForms
import RamanujanTau.Realize
import RamanujanTau.RamanujanODE.QSeries

/-! Exact Euler products and their analytic q-expansions. -/

set_option autoImplicit false

namespace RamanujanTau.TheoremA.EtaSquared
open ModularForm Realize RamanujanODEProof
open UpperHalfPlane hiding I
open Complex hiding eta
open scoped Real Manifold
local notation "𝕢" => Function.Periodic.qParam

noncomputable def qLift (f : ℂ → ℂ) (z : ℍ) : ℂ := f (𝕢 1 z)

lemma qParam_mem_disc (z : ℍ) : 𝕢 1 z ∈ Metric.ball (0 : ℂ) 1 := by
  simpa [Function.Periodic.qParam, mem_ball_zero_iff] using norm_exp_two_pi_I_lt_one z

lemma realizes_qLift_series {f : ℂ → ℂ} {F : PowerSeries ℤ} (hf : Realizes f F) :
    IsQSeries (qLift f) (fun n => (F.coeff n : ℂ)) := by
  intro z
  simpa [qLift, smul_eq_mul] using hf.hasSum (qParam_mem_disc z)

lemma realizes_qLift_holo {f : ℂ → ℂ} {F : PowerSeries ℤ} (hf : Realizes f F) :
    MDiff (qLift f) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hd : DifferentiableOn ℂ (fun z : ℂ => f (𝕢 1 z)) upperHalfPlaneSet :=
    hf.diff.comp (Function.Periodic.differentiable_qParam (h := 1)).differentiableOn
      (fun z hz => qParam_mem_disc ⟨z, hz⟩)
  refine hd.congr fun z hz => ?_
  simp [qLift, ofComplex_apply_of_im_pos hz]

theorem qExpansion_qLift {f : ℂ → ℂ} {F : PowerSeries ℤ} (hf : Realizes f F) :
    qExpansion 1 (qLift f) = PowerSeries.map (Int.castRingHom ℂ) F := by
  rw [(realizes_qLift_series hf).qExpansion_eq (realizes_qLift_holo hf)]
  ext n
  simp

lemma qLift_analytic {f : ℂ → ℂ} {F : PowerSeries ℤ} (hf : Realizes f F) :
    AnalyticAt ℂ (cuspFunction 1 (qLift f)) 0 :=
  (realizes_qLift_series hf).analyticAt (realizes_qLift_holo hf)

lemma qParam_scale (d : ℕ) (hd : 0 < d) (z : ℍ) :
    𝕢 1 (scale d hd z) = 𝕢 1 z ^ d := by
  simp only [Function.Periodic.qParam, scale, Complex.ofReal_one, div_one]
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

lemma scaledEta_qProduct (d : ℕ) (hd : 0 < d) (z : ℍ) :
    scaledEta d hd z = Complex.exp (π * I * (d : ℂ) * z / 6) *
      Pfun d d (𝕢 1 z) ^ 2 := by
  have hp : (∏' n, (1 - eta_q n (scale d hd z))) = Pfun d d (𝕢 1 z) := by
    apply tprod_congr
    intro n
    rw [eta_q, qParam_scale, ← pow_mul]
    congr 2
    ring
  unfold scaledEta etaSquared eta
  rw [mul_pow, hp]
  congr 1
  simp only [Function.Periodic.qParam, scale]
  rw [← Complex.exp_nat_mul]
  congr 1
  norm_num
  ring

lemma basis_weighted_exponent (a : Fin 3) :
    ∑ j : Fin 4, (dilation j : ℤ) * basisExponent a j = 12 * (a.val + 1 : ℕ) := by
  revert a
  decide +kernel

theorem basisFunction_qProduct (a : Fin 3) (z : ℍ) :
    basisFunction a z = 𝕢 1 z ^ (a.val + 1) *
      ∏ j : Fin 4, Pfun (dilation j) (dilation j) (𝕢 1 z) ^ (2 * basisExponent a j) := by
  simp only [basisFunction, scaledEta_qProduct, mul_zpow, Finset.prod_mul_distrib]
  congr 1
  · simp_rw [← Complex.exp_int_mul]
    rw [← Complex.exp_sum]
    simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
    rw [← Complex.exp_nat_mul]
    congr 1
    have hs : (∑ j : Fin 4, (dilation j : ℂ) * basisExponent a j) =
        12 * (a.val + 1 : ℕ) := by exact_mod_cast basis_weighted_exponent a
    calc
      _ = (π * I * z / 6) * ∑ j : Fin 4, (dilation j : ℂ) * basisExponent a j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [hs]; push_cast; ring
  · apply Finset.prod_congr rfl
    intro j _
    rw [← zpow_natCast, ← zpow_mul]
    norm_num

lemma Pfun_qParam_ne_zero (d : ℕ) (hd : 0 < d) (z : ℍ) : Pfun d d (𝕢 1 z) ≠ 0 := by
  intro h
  have he := scaledEta_ne_zero d hd z
  rw [scaledEta_qProduct, h, zero_pow (by decide), mul_zero] at he
  exact he rfl

lemma basis_zero_qProduct (z : ℍ) : basisFunction 0 z =
    𝕢 1 z * Pfun 1 1 (𝕢 1 z) ^ 6 * Pfun 3 3 (𝕢 1 z) ^ 6 := by
  rw [basisFunction_qProduct]
  norm_num [Fin.prod_univ_succ, dilation, basisExponent]
  ring_nf
  rfl

lemma basis_one_qProduct (z : ℍ) : basisFunction 1 z =
    𝕢 1 z ^ 2 * Pfun 2 2 (𝕢 1 z) ^ 6 * Pfun 6 6 (𝕢 1 z) ^ 6 := by
  rw [basisFunction_qProduct]
  norm_num [Fin.prod_univ_succ, dilation, basisExponent]
  ring_nf
  rfl

lemma basis_two_qProduct (z : ℍ) :
    basisFunction 2 z * (Pfun 2 2 (𝕢 1 z) ^ 2 * Pfun 3 3 (𝕢 1 z) ^ 4) =
      𝕢 1 z ^ 3 * Pfun 1 1 (𝕢 1 z) ^ 4 * Pfun 6 6 (𝕢 1 z) ^ 14 := by
  rw [basisFunction_qProduct]
  norm_num [Fin.prod_univ_succ, dilation, basisExponent]
  field_simp [Pfun_qParam_ne_zero 2 (by decide) z, Pfun_qParam_ne_zero 3 (by decide) z]

end RamanujanTau.TheoremA.EtaSquared
