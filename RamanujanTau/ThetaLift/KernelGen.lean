import RamanujanTau.ThetaLift.KernelUniform
import RamanujanTau.ThetaLift.KernelCovariance

/-!
# The generating identity of the kernel and its Taylor coefficients

Poisson summation in `c` is carried out on all of `ℤ³`, without excluding `(a,m) = (0,0)`. The
coefficient of `σⁿ` on the lattice side is the kernel with `Qⁿ` in its summand.
-/

set_option autoImplicit false

namespace RamanujanTau.ThetaLift
open Complex
open scoped Real

noncomputable section

namespace KData
variable (D : KData)

/-- The sum over `b` of the dual term. -/
def dF (a m : ℤ) : ℂ := ∑' b : ℤ, D.dualF a b m

lemma summable_dualTriple : Summable fun x : ℤ × ℤ × ℤ => D.dualF x.1 x.2.1 x.2.2 := by
  have h := D.summable_uDual (‖D.σ‖ + 1)
  refine Summable.of_norm_bounded h fun x => ?_
  have hmem : D.σ ∈ Metric.ball (0 : ℂ) (‖D.σ‖ + 1) := by simp
  exact D.norm_dualF_le hmem x

/-- The reordering of `ℤ³` that groups `b` last. -/
def eAMB : (ℤ × ℤ) × ℤ ≃ ℤ × ℤ × ℤ where
  toFun p := (p.1.1, p.2, p.1.2)
  invFun x := ((x.1, x.2.2), x.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The dominating family of the sums over `b`. -/
def uD (R : ℝ) (p : ℤ × ℤ) : ℝ := ∑' b : ℤ, D.uDual R (eAMB (p, b))

lemma summable_uD (R : ℝ) : Summable (D.uD R) :=
  ((eAMB.summable_iff (f := D.uDual R)).mpr (D.summable_uDual R)).prod

lemma summable_uDual_fiber (R : ℝ) (p : ℤ × ℤ) : Summable fun b : ℤ => D.uDual R (eAMB (p, b)) :=
  ((eAMB.summable_iff (f := D.uDual R)).mpr (D.summable_uDual R)).prod_factor p

lemma norm_dF_le {R : ℝ} {τ : ℂ} (hτ : τ ∈ Metric.ball (0 : ℂ) R) (p : ℤ × ℤ) :
    ‖(D.atσ τ).dF p.1 p.2‖ ≤ D.uD R p := by
  have hb : ∀ b : ℤ, ‖(D.atσ τ).dualF p.1 b p.2‖ ≤ D.uDual R (eAMB (p, b)) := fun b =>
    D.norm_dualF_le hτ (eAMB (p, b))
  exact tsum_of_norm_bounded (D.summable_uDual_fiber R p).hasSum hb

lemma dualF_differentiable (a b m : ℤ) :
    Differentiable ℂ fun τ : ℂ => (D.atσ τ).dualF a b m := by
  change Differentiable ℂ fun τ : ℂ => (chiZ (D.N * b) : ℂ) *
    cexp (2 * π * I * (D.N * b ^ 2 / 24) * D.Zc +
      ((I * τ / (D.N * D.z * D.y)) * I * D.τ₂ a b - D.κ * D.τ₂ a b ^ 2 +
        2 * π * I * D.τ₁ a b * (a * D.Zc + m) +
        (I * τ / (D.N * D.z * D.y)) ^ 2 / (4 * D.κ) -
        π * I * (I * τ / (D.N * D.z * D.y)) * (a * D.Zc + m) / D.κ -
        π ^ 2 * (a * D.Zc + m) ^ 2 / D.κ))
  fun_prop

lemma dF_differentiable (a m : ℤ) : Differentiable ℂ fun τ : ℂ => (D.atσ τ).dF a m := by
  intro τ
  have hU : Metric.ball (0 : ℂ) (‖τ‖ + 1) ∈ nhds τ := Metric.isOpen_ball.mem_nhds (by simp)
  have h := Complex.differentiableOn_tsum_of_summable_norm
    (F := fun (b : ℤ) (t : ℂ) => (D.atσ t).dualF a b m)
    (D.summable_uDual_fiber (‖τ‖ + 1) (a, m))
    (fun b => (D.dualF_differentiable a b m).differentiableOn) Metric.isOpen_ball
    (fun b t ht => D.norm_dualF_le ht (eAMB ((a, m), b)))
  exact h.differentiableAt hU

/-- **The generating identity on `ℤ³`.** -/
theorem gen_eq_dual (ψ : ℤ → ℂ) (hψ : ∀ a, ‖ψ a‖ ≤ 1) :
    ∑' x : ℤ × ℤ × ℤ, ψ x.1 * ((chiZ (D.N * x.2.1) : ℂ) * D.latTerm x.1 x.2.1 x.2.2) =
      ((√(π / D.κ) : ℝ) : ℂ) * ∑' p : ℤ × ℤ, ψ p.1 * D.dF p.1 p.2 := by
  have hχ : ∀ x : ℤ, ‖((chiZ x : ℤ) : ℂ)‖ ≤ 1 := chiZ_norm
  have hS : Summable fun x : ℤ × ℤ × ℤ =>
      ψ x.1 * ((chiZ (D.N * x.2.1) : ℂ) * D.latTerm x.1 x.2.1 x.2.2) := by
    refine Summable.of_norm_bounded D.summable_latTerm.norm fun x => ?_
    rw [norm_mul, norm_mul]
    calc _ ≤ 1 * (1 * ‖D.latTerm x.1 x.2.1 x.2.2‖) := by
          gcongr
          · exact hψ _
          · exact hχ _
      _ = _ := by ring
  have hT : Summable fun x : ℤ × ℤ × ℤ => ψ x.1 * D.dualF x.1 x.2.1 x.2.2 := by
    refine Summable.of_norm_bounded D.summable_dualTriple.norm fun x => ?_
    rw [norm_mul]
    calc _ ≤ 1 * ‖D.dualF x.1 x.2.1 x.2.2‖ := by
          gcongr
          exact hψ _
      _ = _ := one_mul _
  have hbc : ∀ a b : ℤ, ∑' c : ℤ, (chiZ (D.N * b) : ℂ) * D.latTerm a b c =
      ((√(π / D.κ) : ℝ) : ℂ) * ∑' m : ℤ, D.dualF a b m := by
    intro a b
    have hF : ∀ m : ℤ, D.dualF a b m = ((chiZ (D.N * b) : ℂ) *
        cexp (2 * π * I * (D.N * b ^ 2 / 24) * D.Zc)) * cexp (D.dualE a b m) := by
      intro m
      unfold dualF
      rw [Complex.exp_add]
      ring
    have hS' : ∑' m : ℤ, D.dualF a b m = ((chiZ (D.N * b) : ℂ) *
        cexp (2 * π * I * (D.N * b ^ 2 / 24) * D.Zc)) * ∑' m : ℤ, cexp (D.dualE a b m) := by
      rw [← tsum_mul_left]
      exact tsum_congr hF
    rw [hS', tsum_mul_left, D.tsum_latTerm]
    ring
  have hL : ∑' x : ℤ × ℤ × ℤ, ψ x.1 * ((chiZ (D.N * x.2.1) : ℂ) * D.latTerm x.1 x.2.1 x.2.2) =
      ∑' a : ℤ, ψ a * (((√(π / D.κ) : ℝ) : ℂ) * ∑' m : ℤ, ∑' b : ℤ, D.dualF a b m) := by
    have hfib : ∀ a : ℤ, Summable fun p : ℤ × ℤ =>
        ψ a * ((chiZ (D.N * p.1) : ℂ) * D.latTerm a p.1 p.2) := fun a => hS.prod_factor a
    rw [hS.tsum_prod' hfib]
    refine tsum_congr fun a => ?_
    change ∑' p : ℤ × ℤ, ψ a * ((chiZ (D.N * p.1) : ℂ) * D.latTerm a p.1 p.2) = _
    rw [tsum_mul_left]
    congr 1
    have hχS : Summable fun p : ℤ × ℤ => (chiZ (D.N * p.1) : ℂ) * D.latTerm a p.1 p.2 := by
      refine Summable.of_norm_bounded (D.summable_latTerm.norm.prod_factor a) fun p => ?_
      rw [norm_mul]
      calc _ ≤ 1 * ‖D.latTerm a p.1 p.2‖ := by
            gcongr
            exact hχ _
        _ = _ := one_mul _
    rw [hχS.tsum_prod' fun b => hχS.prod_factor b, tsum_congr (hbc a), tsum_mul_left]
    congr 1
    exact (Summable.tsum_comm (f := fun b m => D.dualF a b m) (D.summable_dualF a)).symm
  have hT' := (eAMB.summable_iff (f := fun x : ℤ × ℤ × ℤ => ψ x.1 * D.dualF x.1 x.2.1 x.2.2)).mpr hT
  have hp : ∀ p : ℤ × ℤ, ∑' b : ℤ, (fun x : ℤ × ℤ × ℤ => ψ x.1 * D.dualF x.1 x.2.1 x.2.2) (eAMB (p, b)) =
      ψ p.1 * D.dF p.1 p.2 := by
    intro p
    change ∑' b : ℤ, ψ p.1 * D.dualF p.1 b p.2 = _
    rw [tsum_mul_left]
    rfl
  have hPS : Summable fun p : ℤ × ℤ => ψ p.1 * D.dF p.1 p.2 := hT'.prod.congr hp
  have hR : ∑' p : ℤ × ℤ, ψ p.1 * D.dF p.1 p.2 = ∑' a : ℤ, ψ a * ∑' m : ℤ, ∑' b : ℤ, D.dualF a b m := by
    rw [hPS.tsum_prod' fun a => hPS.prod_factor a]
    refine tsum_congr fun a => ?_
    change ∑' m : ℤ, ψ a * D.dF a m = _
    rw [tsum_mul_left]
    rfl
  rw [hL, hR, ← tsum_mul_left]
  refine tsum_congr fun a => ?_
  ring

/-- **Taylor coefficients of the dual side.** -/
theorem taylor_dual (ψ : ℤ → ℂ) (hψ : ∀ a, ‖ψ a‖ ≤ 1) (n : ℕ) :
    HasSum (fun p : ℤ × ℤ => ψ p.1 * iteratedDeriv n (fun τ => (D.atσ τ).dF p.1 p.2) 0)
      (iteratedDeriv n (fun τ => ∑' p : ℤ × ℤ, ψ p.1 * (D.atσ τ).dF p.1 p.2) 0) := by
  have h := hasSum_iteratedDeriv (F := fun (p : ℤ × ℤ) τ => ψ p.1 * (D.atσ τ).dF p.1 p.2)
    (D.summable_uD 1) (U := Metric.ball (0 : ℂ) 1) Metric.isOpen_ball
    (fun p => (D.dF_differentiable p.1 p.2).const_mul _)
    (fun p τ hτ => by
      rw [norm_mul]
      calc _ ≤ 1 * D.uD 1 p := mul_le_mul (hψ _) (D.norm_dF_le hτ p) (norm_nonneg _) zero_le_one
        _ = _ := one_mul _) n (Metric.mem_ball_self one_pos)
  convert h using 2 with p
  exact (iteratedDeriv_const_mul_field _ _).symm

/-- The scale of the generating parameter. -/
def sc : ℂ := I / (D.N * D.z * D.y)

/-- The form at `w = ξ + iy`, in lattice coordinates. -/
lemma kQ_eq (a b c : ℤ) :
    kQ D.N a b c ((D.ξ : ℂ) + D.y * I) = (c : ℂ) + D.τ₁ a b + I * D.τ₂ a b := by
  unfold kQ τ₁ τ₂
  simp only [map_add, map_mul, conj_ofReal, conj_I]
  push_cast
  linear_combination (6 * (D.N : ℂ) * a * D.y ^ 2) * Complex.I_sq

lemma normSq_kQ (a b c : ℤ) :
    ((normSq (kQ D.N a b c ((D.ξ : ℂ) + D.y * I)) : ℝ) : ℂ) =
      ((c : ℂ) + D.τ₁ a b) ^ 2 + D.τ₂ a b ^ 2 := by
  rw [D.kQ_eq]
  have e : (c : ℂ) + D.τ₁ a b + I * D.τ₂ a b = (((c : ℝ) + D.τ₁ a b : ℝ) : ℂ) + (D.τ₂ a b : ℝ) * I := by
    push_cast
    ring
  rw [e, Complex.normSq_add_mul_I]
  push_cast
  rfl

/-- A lattice term as an exponential that is linear in `τ`. -/
lemma latTerm_atσ (a b c : ℤ) (τ : ℂ) :
    (D.atσ τ).latTerm a b c = cexp ((D.sc * ((c : ℂ) + D.τ₁ a b + I * D.τ₂ a b)) * τ +
      (-(D.κ * (((c : ℂ) + D.τ₁ a b) ^ 2 + D.τ₂ a b ^ 2)) +
        2 * π * I * (D.N * b ^ 2 / 24 - a * c) * D.Zc)) := by
  change cexp ((I * τ / (D.N * D.z * D.y)) * (c + D.τ₁ a b + I * D.τ₂ a b) -
    D.κ * (((c : ℂ) + D.τ₁ a b) ^ 2 + D.τ₂ a b ^ 2) +
    2 * π * I * (D.N * b ^ 2 / 24 - a * c) * D.Zc) = _
  congr 1
  unfold sc
  ring

/-- **Taylor coefficients of the lattice side.** -/
theorem taylor_lat (ψ : ℤ → ℂ) (hψ : ∀ a, ‖ψ a‖ ≤ 1) (n : ℕ) :
    HasSum (fun x : ℤ × ℤ × ℤ => D.sc ^ n *
        kTerm ψ D.N D.vt D.Zc n ((D.ξ : ℂ) + D.y * I) x)
      (iteratedDeriv n (fun τ => ∑' x : ℤ × ℤ × ℤ,
        ψ x.1 * ((chiZ (D.N * x.2.1) : ℂ) * (D.atσ τ).latTerm x.1 x.2.1 x.2.2)) 0) := by
  have hχ : ∀ x : ℤ, ‖((chiZ x : ℤ) : ℂ)‖ ≤ 1 := chiZ_norm
  have h := hasSum_iteratedDeriv
    (F := fun (x : ℤ × ℤ × ℤ) τ =>
      ψ x.1 * ((chiZ (D.N * x.2.1) : ℂ) * (D.atσ τ).latTerm x.1 x.2.1 x.2.2))
    (D.summable_uLat 1) (U := Metric.ball (0 : ℂ) 1) Metric.isOpen_ball
    (fun x => by
      simp only [latTerm_atσ]
      fun_prop)
    (fun x τ hτ => by
      rw [norm_mul, norm_mul]
      calc _ ≤ 1 * (1 * D.uLat 1 x) := by
            gcongr
            · exact hψ _
            · exact hχ _
            · exact D.norm_latTerm_le hτ x
        _ = _ := by ring) n (Metric.mem_ball_self one_pos)
  convert h using 2 with x
  obtain ⟨a, b, c⟩ := x
  simp only [latTerm_atσ]
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field, iteratedDeriv_exp_lin]
  have hy : ((D.ξ : ℂ) + D.y * I).im = D.y := by simp
  unfold kTerm
  simp only
  have hk : ((π * D.vt / (6 * ((D.N : ℤ) : ℝ) * ((D.ξ : ℂ) + D.y * I).im ^ 2) *
      normSq (kQ D.N a b c ((D.ξ : ℂ) + D.y * I)) : ℝ) : ℂ) =
      D.κ * (((c : ℂ) + D.τ₁ a b) ^ 2 + D.τ₂ a b ^ 2) := by
    rw [ofReal_mul, D.normSq_kQ, hy]
    congr 2
  rw [hk, D.kQ_eq]
  have hd : (((D.N : ℤ) * b ^ 2 - 24 * (a * c) : ℤ) : ℂ) / 24 = D.N * b ^ 2 / 24 - a * c := by
    push_cast
    ring
  rw [hd, mul_zero, zero_add, mul_pow]
  ring

/-- **The kernel as a sum over `(a,m)`.** -/
theorem kernel_expand (ψ : ℤ → ℂ) (hψ : ∀ a, ‖ψ a‖ ≤ 1) (n : ℕ) :
    D.sc ^ n * ∑' x : ℤ × ℤ × ℤ, kTerm ψ D.N D.vt D.Zc n ((D.ξ : ℂ) + D.y * I) x =
      ((√(π / D.κ) : ℝ) : ℂ) *
        ∑' p : ℤ × ℤ, ψ p.1 * iteratedDeriv n (fun τ => (D.atσ τ).dF p.1 p.2) 0 := by
  rw [← tsum_mul_left, (D.taylor_lat ψ hψ n).tsum_eq, (D.taylor_dual ψ hψ n).tsum_eq]
  have h : (fun τ => ∑' x : ℤ × ℤ × ℤ,
      ψ x.1 * ((chiZ (D.N * x.2.1) : ℂ) * (D.atσ τ).latTerm x.1 x.2.1 x.2.2)) =
      fun τ => ((√(π / D.κ) : ℝ) : ℂ) * ∑' p : ℤ × ℤ, ψ p.1 * (D.atσ τ).dF p.1 p.2 :=
    funext fun τ => (D.atσ τ).gen_eq_dual ψ hψ
  rw [h, iteratedDeriv_const_mul_field]

/-- The sum over `b` at `(a,m)` is the Poincaré term. -/
lemma dF_eq_pTerm (a m : ℤ) (hL : D.L a m ≠ 0) :
    D.dF a m = (chiZ D.N : ℂ) * (sqrt D.z * e24 (-3)) * D.pTerm a m := by
  unfold dF dualF
  rw [D.tsum_b a m, mul_assoc, D.dual_inverted a m hL]
  ring

end KData

open Rademacher ModularForm MatrixGroups

lemma seed_differentiable (ξ y : ℝ) (g : ℤ) {z : ℂ} (hz : 0 < z.im) :
    Differentiable ℂ (seed ξ y g z) := by
  intro σ
  have hR : 0 < ‖σ‖ + 1 := by positivity
  have hK : 0 < π * z.im / 12 := by
    have := Real.pi_pos
    positivity
  have hU : Metric.ball (0 : ℂ) (‖σ‖ + 1) ∈ nhds σ := Metric.isOpen_ball.mem_nhds (by simp)
  have hu := ((summable_seed_bound hK (‖σ‖ + 1)).add
    (summable_seed_bound hK (-(‖σ‖ + 1)))).mul_left
    (Real.exp (-(6 * π * g ^ 2 * y ^ 2 / z.im) +
      ‖(6 * g * y / z.im : ℂ)‖ * (‖σ‖ + 1) + ‖sB z ^ 2‖ * (‖σ‖ + 1) ^ 2 / 2))
  have h := Complex.differentiableOn_tsum_of_summable_norm (F := sF ξ y g z) hu
    (fun x => (sF_differentiable ξ y g z x).differentiableOn) Metric.isOpen_ball
    (fun x τ hτ => norm_sF_le ξ y g hz hR x hτ)
  have he : seed ξ y g z = fun τ => ∑' x : ℤ, sF ξ y g z x τ :=
    funext fun τ => seed_eq_tsum ξ y g hz τ
  rw [he]
  exact h.differentiableAt hU

/-- **The Taylor coefficient of the term `(a,m)`**, as a translate of the Hermite theta series. -/
theorem KData.dF_taylor (D : KData) (γ : SL(2, ℤ)) (g a m : ℤ) (hg : g ≠ 0)
    (hc : (D.N : ℤ) * m = g * γ 1 0) (hd : a = -g * γ 1 1) (n : ℕ) :
    iteratedDeriv n (fun τ => (D.atσ τ).dF a m) 0 =
      (chiZ D.N : ℂ) * (sqrt D.z * e24 (-3)) * (η D.z / η (mob γ D.z)) * (lin γ D.z)⁻¹ ^ n *
        iteratedDeriv n (seed D.ξ D.y g (mob γ D.z)) 0 := by
  have hj : lin γ D.z ≠ 0 := denom_ne_zero' γ D.hz
  have hγz : 0 < (mob γ D.z).im := by
    have hmob : mob γ D.z = (((γ • (⟨D.z, D.hz⟩ : UpperHalfPlane)) : UpperHalfPlane) : ℂ) :=
      mob_eq γ (⟨D.z, D.hz⟩ : UpperHalfPlane)
    rw [hmob]
    exact (γ • (⟨D.z, D.hz⟩ : UpperHalfPlane)).2
  have hη : η (mob γ D.z) ≠ 0 := eta_ne_zero hγz
  have hL : D.L a m ≠ 0 := by
    have hLg : D.L a m = g * lin γ D.z := by
      have hcC : (D.N : ℂ) * m = g * γ 1 0 := by exact_mod_cast hc
      have hdC : (a : ℂ) = -g * γ 1 1 := by exact_mod_cast hd
      unfold KData.L lin
      rw [hcC, hdC]
      ring
    rw [hLg]
    exact mul_ne_zero (by exact_mod_cast hg) hj
  have hF : (fun τ => (D.atσ τ).dF a m) = fun τ =>
      ((chiZ D.N : ℂ) * (sqrt D.z * e24 (-3)) * (η D.z / η (mob γ D.z))) *
        seed D.ξ D.y g (mob γ D.z) ((lin γ D.z)⁻¹ * τ) := by
    funext τ
    have h1 := (D.atσ τ).dF_eq_pTerm a m hL
    have h2 := (D.atσ τ).pTerm_eq γ g a m hg hc hd
    change (D.atσ τ).dF a m = _
    rw [h1]
    change (chiZ D.N : ℂ) * (sqrt D.z * e24 (-3)) * (D.atσ τ).pTerm a m = _
    have h3 : (D.atσ τ).pTerm a m = seed D.ξ D.y g (mob γ D.z) (τ / lin γ D.z) * η D.z /
        η (mob γ D.z) := by
      rw [eq_div_iff hη]
      exact h2
    rw [h3, div_eq_inv_mul τ]
    ring
  rw [hF, iteratedDeriv_const_mul_field,
    congrFun (iteratedDeriv_comp_const_mul
      ((seed_differentiable D.ξ D.y g hγz).contDiff (n := n)) _) 0]
  simp only [mul_zero]
  ring

end

end RamanujanTau.ThetaLift
