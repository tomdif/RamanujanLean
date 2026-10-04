/-
# The analytic–formal bridge for `Δ = η²⁴`: `qExpansion(Δ).coeff n = τ(n)` for every `n`

Mathlib's modular discriminant `Δ` is an *analytic* object (`η²⁴`, a function on `ℍ`); the repo's `τ` is the
coefficient sequence of the *formal* power series `q ∏_{k≥1}(1 − qᵏ)²⁴ ∈ ℤ⟦q⟧` (`TauCong.tauPS`). This file
identifies them coefficient by coefficient:

  **`qExpansion_discriminant_coeff`:**  `(qExpansion 1 Δ).coeff n = τ(n)`   for all `n`.

Route (no `FormalMultilinearSeries` for infinite products needed):
* the cusp function of `Δ` is `q ↦ q·∏'(1 − qᵏ⁺¹)²⁴` on the unit disc (`DiscriminantBridge`);
* the polynomial partial products `F_N(q) = q·(∏_{k<N}(1 − qᵏ⁺¹))²⁴` converge to it locally uniformly there;
* by Weierstrass (`TendstoLocallyUniformlyOn.deriv`, iterated), `iteratedDeriv n F_N 0 → iteratedDeriv n (cusp) 0`;
* `iteratedDeriv n F_N 0 = n!·[qⁿ]F_N`, and `[qⁿ]F_N = τ(n)` as soon as `N > n` (coefficient stabilization).

This closes item 2 of `OPEN_QUESTIONS.md`, previously recorded as an infrastructure gap.
-/
import RamanujanTau.DiscriminantBridge
import RamanujanTau.TauCongruences
import Mathlib.Analysis.Complex.LocallyUniformLimit

set_option autoImplicit false

namespace RamanujanTau.DiscriminantBridge
open Complex Filter Metric Function Set ModularForm UpperHalfPlane
open scoped Topology

/-! ### Analytic lemmas -/

/-- iterated derivatives commute with locally uniform limits of holomorphic functions. -/
lemma tlu_iteratedDeriv {U : Set ℂ} (hU : IsOpen U) (n : ℕ) :
    ∀ {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}, TendstoLocallyUniformlyOn F f atTop U →
      (∀ N, DifferentiableOn ℂ (F N) U) →
      TendstoLocallyUniformlyOn (fun N => iteratedDeriv n (F N)) (iteratedDeriv n f) atTop U := by
  induction n with
  | zero => intro F f hF _; simpa using hF
  | succ n ih =>
    intro F f hF hd
    simp_rw [iteratedDeriv_succ']
    exact ih (hF.deriv (Eventually.of_forall hd) hU) (fun N => (hd N).deriv hU)

lemma eventuallyEq_iteratedDeriv {f g : ℂ → ℂ} {x : ℂ} (h : f =ᶠ[𝓝 x] g) (n : ℕ) :
    iteratedDeriv n f =ᶠ[𝓝 x] iteratedDeriv n g := by
  induction n with
  | zero => simpa using h
  | succ n ih => simp_rw [iteratedDeriv_succ]; exact ih.deriv

lemma iteratedDeriv_poly (p : Polynomial ℂ) (n : ℕ) :
    iteratedDeriv n (fun x => p.eval x) = fun x => (Polynomial.derivative^[n] p).eval x := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ', show deriv (fun x => p.eval x) = fun x => (Polynomial.derivative p).eval x from
      funext fun x => Polynomial.deriv p, ih, Function.iterate_succ_apply]

lemma iteratedDeriv_poly_zero (p : Polynomial ℂ) (n : ℕ) :
    iteratedDeriv n (fun x => p.eval x) 0 = n.factorial * p.coeff n := by
  rw [iteratedDeriv_poly]
  dsimp only
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative, zero_add,
    Nat.descFactorial_self, nsmul_eq_mul]

lemma tlu_const {U : Set ℂ} (f : ℂ → ℂ) : TendstoLocallyUniformlyOn (fun (_ : ℕ) => f) f atTop U :=
  TendstoUniformlyOn.tendstoLocallyUniformlyOn
    (fun _ hu => Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu)

lemma tlu_pow {U : Set ℂ} {G : ℕ → ℂ → ℂ} {g : ℂ → ℂ} (hG : TendstoLocallyUniformlyOn G g atTop U)
    (hg : ContinuousOn g U) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun N q => G N q ^ k) (fun q => g q ^ k) atTop U := by
  induction k with
  | zero => simpa using tlu_const (U := U) (fun _ : ℂ => (1 : ℂ))
  | succ k ih =>
    simp_rw [pow_succ]
    exact ih.mul₀ hG (hg.pow k) hg

/-! ### The polynomial partial products -/

/-- `q·(∏_{k<N}(1 − qᵏ⁺¹))²⁴` as an integer polynomial. -/
noncomputable def PN (N : ℕ) : Polynomial ℤ :=
  Polynomial.X * (∏ k ∈ Finset.range N, (1 - Polynomial.X ^ (k + 1))) ^ 24

lemma coe_PN (N : ℕ) : ((PN N : Polynomial ℤ) : PowerSeries ℤ) = PowerSeries.X * MockTheta5.Bailey.qfac N ^ 24 := by
  rw [PN, MockTheta5.Bailey.qfac, ← Polynomial.coeToPowerSeries.ringHom_apply, map_mul, map_pow, map_prod]
  simp

lemma PN_coeff {n N : ℕ} (hN : n + 1 ≤ N) : (PN N).coeff n = TauCong.tauPS n := by
  rw [← Polynomial.coeff_coe, coe_PN, TauCong.tauPS, ← sub_eq_zero, ← map_sub]
  have h1 : PowerSeries.X ^ (n + 1) ∣ MockTheta5.Bailey.qfac N - MockTheta5.JTP.qfacInf := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    rw [map_sub, MockTheta5.JTP.coeff_qfacInf (by omega : m + 1 ≤ N), sub_self]
  have h2 : PowerSeries.X ^ (n + 1) ∣
      PowerSeries.X * MockTheta5.Bailey.qfac N ^ 24 - PowerSeries.X * MockTheta5.JTP.qfacInf ^ 24 := by
    rw [← mul_sub]
    exact dvd_mul_of_dvd_right (h1.trans (sub_dvd_pow_sub_pow _ _ 24)) _
  exact PowerSeries.X_pow_dvd_iff.mp h2 n (Nat.lt_succ_self n)

/-- the complex partial products. -/
noncomputable def FN (N : ℕ) (q : ℂ) : ℂ := ((PN N).map (Int.castRingHom ℂ)).eval q

lemma FN_eq (N : ℕ) (q : ℂ) : FN N q = q * (∏ k ∈ Finset.range N, (1 - q ^ (k + 1))) ^ 24 := by
  simp [FN, PN, Polynomial.map_prod, Polynomial.eval_prod]

/-- the limit function `q·(∏'(1 − qᵏ⁺¹))²⁴`. -/
noncomputable def Flim (q : ℂ) : ℂ := q * (∏' k : ℕ, (1 - q ^ (k + 1))) ^ 24

lemma tlu_FN : TendstoLocallyUniformlyOn FN Flim atTop (ball (0 : ℂ) 1) := by
  have hP := multipliableLocallyUniformlyOn_one_sub_pow.hasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange
  have hc : ContinuousOn (fun q : ℂ => ∏' k : ℕ, (1 - q ^ (k + 1))) (ball (0 : ℂ) 1) :=
    differentiableOn_tprod_one_sub_pow.continuousOn
  have h24 := tlu_pow hP hc 24
  have hid : TendstoLocallyUniformlyOn (fun (_ : ℕ) (q : ℂ) => q) (fun q => q) atTop (ball (0 : ℂ) 1) :=
    tlu_const _
  have := hid.mul₀ h24 continuousOn_id (hc.pow 24)
  convert this using 1
  · funext N q; rw [FN_eq]; rfl

lemma cusp_eventuallyEq : cuspFunction 1 Δmod =ᶠ[𝓝 0] Flim := by
  filter_upwards [ball_mem_nhds (0 : ℂ) one_pos] with q hq
  have hq' : ‖q‖ < 1 := by simpa using hq
  rw [cuspFunction_Δmod_eq hq', Flim, Gprod, (multipliable_one_sub_pow hq').tprod_pow 24]

/-- **The analytic–formal bridge.** The `n`-th q-expansion coefficient of Mathlib's modular discriminant
`Δ = η²⁴` is `τ(n) = [qⁿ] q∏(1 − qᵏ)²⁴`. -/
theorem qExpansion_discriminant_coeff (n : ℕ) : (qExpansion 1 Δmod).coeff n = (TauCong.tauPS n : ℂ) := by
  rw [qExpansion_coeff, (eventuallyEq_iteratedDeriv cusp_eventuallyEq n).eq_of_nhds]
  have hlim := (tlu_iteratedDeriv isOpen_ball n tlu_FN
    (fun N => (Polynomial.differentiable _).differentiableOn)).tendsto_at (mem_ball_self one_pos)
  have hconst : ∀ᶠ N in atTop, iteratedDeriv n (FN N) 0 = n.factorial * (TauCong.tauPS n : ℂ) := by
    filter_upwards [eventually_ge_atTop (n + 1)] with N hN
    rw [show FN N = fun q => ((PN N).map (Int.castRingHom ℂ)).eval q from rfl, iteratedDeriv_poly_zero,
      Polynomial.coeff_map, PN_coeff hN, eq_intCast]
  have := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (EventuallyEq.symm hconst))
  rw [this, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast n.factorial_ne_zero), one_mul]

end RamanujanTau.DiscriminantBridge
