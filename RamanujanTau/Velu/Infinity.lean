import RamanujanTau.Velu.Poly
import Mathlib.FieldTheory.RatFunc.Valuation

/-!
# Vélu: behaviour at infinity and the global identity

In `K(x)` put `X = x + Σ (t_Q/(x-x_Q) + u_Q/(x-x_Q)²)`, `X' = 1 - Σ (t_Q/(x-x_Q)² + 2u_Q/(x-x_Q)³)`
and `F = f X'² - X³ - A' X - B'`. Then `Pv = D⁶ F` and, by the choice `A' = A - 5t`,
`B' = B - 7w`, `F = ζ W` with `ζ = 1/x` and `W` integral at infinity, so `v_∞(F) < 1`.
Together with `D⁶ ∣ Pv` (no poles at the kernel points) this forces `Pv = 0` (`Pv_eq_zero`).
-/

set_option linter.unusedSimpArgs false

namespace Velu

open Polynomial WeierstrassCurve

/-- Expansion at infinity: abstract ring identity (`x ζ = 1`). -/
theorem infty_identity {R : Type*} [CommRing R] (x z M Nn A B t w : R) (hxz : x * z = 1) :
    (x ^ 3 + A * x + B) * (1 - t * z ^ 2 - 2 * w * z ^ 3 - z ^ 4 * Nn) ^ 2 -
        (x + t * z + w * z ^ 2 + z ^ 3 * M) ^ 3 - (A - 5 * t) * (x + t * z + w * z ^ 2 + z ^ 3 * M) -
        (B - 7 * w) =
      z * (-2 * Nn - 3 * M + (1 + A * z ^ 2 + B * z ^ 3) * (t + 2 * w * z + z ^ 2 * Nn) ^ 2 -
        2 * (A + B * z) * (t + 2 * w * z + z ^ 2 * Nn) - 3 * (t + w * z + z ^ 2 * M) ^ 2 -
        z ^ 2 * (t + w * z + z ^ 2 * M) ^ 3 - (A - 5 * t) * (t + w * z + z ^ 2 * M)) := by
  linear_combination (A*Nn^2*z^7 + 2*A*Nn*t*z^5 + 4*A*Nn*w*z^6 - 2*A*Nn*z^3 + A*t^2*z^3 + 4*A*t*w*z^4 - 2*A*t*z + 4*A*w^2*z^5 - 4*A*w*z^2 - 3*M^2*z^5 - 6*M*t*z^3 - 6*M*w*z^4 - 3*M*x*z^2 - 3*M*z + Nn^2*x^2*z^7 + Nn^2*x*z^6 + Nn^2*z^5 + 2*Nn*t*x^2*z^5 + 2*Nn*t*x*z^4 + 2*Nn*t*z^3 + 4*Nn*w*x^2*z^6 + 4*Nn*w*x*z^5 + 4*Nn*w*z^4 - 2*Nn*x^2*z^3 - 2*Nn*x*z^2 - 2*Nn*z + t^2*x^2*z^3 + t^2*x*z^2 - 2*t^2*z + 4*t*w*x^2*z^4 + 4*t*w*x*z^3 - 2*t*w*z^2 - 2*t*x^2*z - 5*t*x + 4*w^2*x^2*z^5 + 4*w^2*x*z^4 + w^2*z^3 - 4*w*x^2*z^2 - 7*w*x*z - 7*w) * hxz

theorem infty_term1 {R : Type*} [CommRing R] (tt u a z e : R) (he : e = 1 + a * z * e) :
    tt * (z * e) + u * (z * e) ^ 2 =
      tt * z + (tt * a + u) * z ^ 2 + z ^ 3 * (tt * a ^ 2 * e + u * a * e * (e + 1)) := by
  linear_combination (z * (a * tt * z + e * u * z + tt + u * z)) * he

theorem infty_term2 {R : Type*} [CommRing R] (tt u a z e : R) (he : e = 1 + a * z * e) :
    tt * (z * e) ^ 2 + 2 * u * (z * e) ^ 3 =
      tt * z ^ 2 + 2 * (u + tt * a) * z ^ 3 +
        z ^ 4 * (tt * a ^ 2 * e * (e + 2) + 2 * u * a * e * (e ^ 2 + e + 1)) := by
  linear_combination (z ^ 2 * (a * e * tt * z + 2 * a * tt * z + 2 * e ^ 2 * u * z + e * tt +
    2 * e * u * z + tt + 2 * u * z)) * he

theorem sum_lin3 {ι R : Type*} [CommRing R] (T : Finset ι) (f1 f2 f3 : ι → R) (c1 c2 c3 : R) :
    ∑ i ∈ T, (f1 i * c1 + f2 i * c2 + c3 * f3 i) =
      (∑ i ∈ T, f1 i) * c1 + (∑ i ∈ T, f2 i) * c2 + c3 * ∑ i ∈ T, f3 i := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih => simp only [Finset.sum_insert ha, ih]; ring

/-- Membership in a subring, by structural recursion on ring expressions. -/
macro "subring_mem" : tactic =>
  `(tactic| repeat' first
    | assumption
    | exact Subring.one_mem _
    | exact ofNat_mem _ _
    | apply Subring.add_mem
    | apply Subring.sub_mem
    | apply Subring.mul_mem
    | apply Subring.pow_mem
    | apply Subring.neg_mem)

variable {K : Type*} [Field K] [DecidableEq K] {A B : K}

namespace Kernel

variable (κ : Kernel A B)

local notation "ψ" => algebraMap K[X] (RatFunc K)

/-- `1/(x - x_Q)` in `K(x)`. -/
noncomputable def ivR (Q : (short A B).Point) : RatFunc K := (ψ (vp Q))⁻¹

/-- Vélu's `X` as a rational function. -/
noncomputable def XR : RatFunc K :=
  RatFunc.X + ∑ Q ∈ κ.S, (RatFunc.C (tQ Q) * ivR Q + RatFunc.C (uQ Q) * ivR Q ^ 2)

/-- `dX/dx` as a rational function. -/
noncomputable def XdR : RatFunc K :=
  1 - ∑ Q ∈ κ.S, (RatFunc.C (tQ Q) * ivR Q ^ 2 + 2 * RatFunc.C (uQ Q) * ivR Q ^ 3)

/-- `F = f X'² - X³ - A' X - B'` as a rational function. -/
noncomputable def FR : RatFunc K :=
  ψ (fpoly A B) * κ.XdR ^ 2 - κ.XR ^ 3 - RatFunc.C κ.A' * κ.XR - RatFunc.C κ.B'

omit [DecidableEq K] in
lemma psi_vp_ne (Q : (short A B).Point) : ψ (vp Q) ≠ 0 :=
  RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero _)

omit [DecidableEq K] in
lemma psi_vp_mul_ivR (Q : (short A B).Point) : ψ (vp Q) * ivR Q = 1 :=
  mul_inv_cancel₀ (psi_vp_ne Q)

lemma psi_D_ne : ψ κ.D ≠ 0 := by
  rw [D, map_prod]
  exact Finset.prod_ne_zero_iff.2 fun Q _ => psi_vp_ne Q

lemma psi_Dq {Q : (short A B).Point} (hQ : Q ∈ κ.S) : ψ (κ.Dq Q) = ψ κ.D * ivR Q := by
  rw [κ.D_eq hQ, map_mul, mul_comm (ψ (vp Q)), mul_assoc, psi_vp_mul_ivR, mul_one]

lemma psi_N : ψ κ.N = ψ κ.D ^ 2 * κ.XR := by
  rw [N, XR, map_add, map_mul, map_pow, RatFunc.algebraMap_X, map_sum, mul_add,
    Finset.mul_sum]
  congr 1
  · ring
  refine Finset.sum_congr rfl fun Q hQ => ?_
  rw [map_mul, map_add, map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_C,
    κ.psi_Dq hQ]
  linear_combination (RatFunc.C (tQ Q) * ψ κ.D ^ 2 * ivR Q) * psi_vp_mul_ivR Q

lemma psi_N1 : ψ κ.N1 = ψ κ.D ^ 3 * κ.XdR := by
  rw [N1, XdR, map_sub, map_pow, map_sum, mul_sub, mul_one, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun Q hQ => ?_
  rw [map_mul, map_add, map_mul, map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_C,
    κ.psi_Dq hQ, map_ofNat]
  linear_combination (RatFunc.C (tQ Q) * ψ κ.D ^ 3 * ivR Q ^ 2) * psi_vp_mul_ivR Q

lemma psi_Pv : ψ κ.Pv = ψ κ.D ^ 6 * κ.FR := by
  rw [Pv, FR, map_sub, map_sub, map_sub, map_mul, map_mul, map_mul, map_mul, map_pow, map_pow,
    map_pow, map_pow, κ.psi_N, κ.psi_N1, RatFunc.algebraMap_C, RatFunc.algebraMap_C]
  ring

omit [DecidableEq K] in
lemma psi_fpoly : ψ (fpoly A B) = RatFunc.X ^ 3 + RatFunc.C A * RatFunc.X + RatFunc.C B := by
  simp [fpoly, RatFunc.algebraMap_X, RatFunc.algebraMap_C]

/-- **Behaviour at infinity**: `v_∞(F) < 1`. -/
theorem FR_val_lt [DecidableEq (RatFunc K)] : RatFunc.inftyValuation K κ.FR < 1 := by
  set v := RatFunc.inftyValuation K with hv
  set z : RatFunc K := RatFunc.X⁻¹ with hz
  have hX0 : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero
  have hxz : RatFunc.X * z = 1 := mul_inv_cancel₀ hX0
  set e : (short A B).Point → RatFunc K := fun Q => RatFunc.X * ivR Q with he_def
  have hiv : ∀ Q, ivR Q = z * e Q := by
    intro Q; simp only [he_def]; rw [← mul_assoc, mul_comm z, hxz, one_mul]
  have he : ∀ Q, e Q = 1 + RatFunc.C (xc Q) * z * e Q := by
    intro Q
    have h1 := psi_vp_mul_ivR Q
    rw [vp, map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C] at h1
    simp only [he_def]
    linear_combination h1 - (RatFunc.C (xc Q) * ivR Q) * hxz
  -- valuations
  have hvz : v z < 1 := by
    rw [hz, map_inv₀, hv, RatFunc.inftyValuation.X]
    rw [← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hzO : z ∈ v.integer := (Valuation.mem_integer_iff _ _).2 hvz.le
  have hCO : ∀ k : K, RatFunc.C k ∈ v.integer := by
    intro k
    rw [Valuation.mem_integer_iff]
    by_cases hk : k = 0
    · simp [hk]
    · rw [RatFunc.inftyValuation.C _ hk]
  have heO : ∀ Q, e Q ∈ v.integer := by
    intro Q
    rw [Valuation.mem_integer_iff]
    simp only [he_def, ivR, map_mul, map_inv₀]
    have : v (ψ (vp Q)) = WithZero.exp 1 := by
      rw [hv, RatFunc.inftyValuation_apply, vp,
        RatFunc.inftyValuation.polynomial _ (X_sub_C_ne_zero _), natDegree_X_sub_C]; rfl
    rw [this, RatFunc.inftyValuation.X, mul_inv_cancel₀ (by simp)]
  -- expansions
  set M := ∑ Q ∈ κ.S, (RatFunc.C (tQ Q) * RatFunc.C (xc Q) ^ 2 * e Q +
    RatFunc.C (uQ Q) * RatFunc.C (xc Q) * e Q * (e Q + 1)) with hM
  set Nn := ∑ Q ∈ κ.S, (RatFunc.C (tQ Q) * RatFunc.C (xc Q) ^ 2 * e Q * (e Q + 2) +
    2 * RatFunc.C (uQ Q) * RatFunc.C (xc Q) * e Q * (e Q ^ 2 + e Q + 1)) with hNn
  have hXR : κ.XR = RatFunc.X + RatFunc.C κ.t * z + RatFunc.C κ.w * z ^ 2 + z ^ 3 * M := by
    rw [XR]
    simp only [hiv]
    rw [Finset.sum_congr rfl fun Q _ => infty_term1 _ _ _ z (e Q) (he Q)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
      ← Finset.mul_sum, t, w, map_sum, map_sum]
    simp only [map_add, map_mul]
    rw [← hM]
    have : ∀ Q ∈ κ.S, RatFunc.C (tQ Q) * RatFunc.C (xc Q) + RatFunc.C (uQ Q) =
        RatFunc.C (uQ Q) + RatFunc.C (xc Q) * RatFunc.C (tQ Q) := fun Q _ => by ring
    rw [Finset.sum_congr rfl this]
    ring
  have hXdR : κ.XdR = 1 - RatFunc.C κ.t * z ^ 2 - 2 * RatFunc.C κ.w * z ^ 3 - z ^ 4 * Nn := by
    rw [XdR]
    simp only [hiv]
    rw [Finset.sum_congr rfl fun Q _ => infty_term2 _ _ _ z (e Q) (he Q), sum_lin3, ← hNn]
    have h1 : ∑ Q ∈ κ.S, RatFunc.C (tQ Q) = RatFunc.C κ.t := by rw [t, map_sum]
    have h2' : ∑ Q ∈ κ.S, 2 * (RatFunc.C (uQ Q) + RatFunc.C (tQ Q) * RatFunc.C (xc Q)) =
        2 * RatFunc.C κ.w := by
      rw [w, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun Q _ => ?_
      simp only [map_add, map_mul]; ring
    rw [h1, h2']
    ring
  have hA' : RatFunc.C κ.A' = RatFunc.C A - 5 * RatFunc.C κ.t := by
    rw [A', map_sub, map_mul, map_ofNat]
  have hB' : RatFunc.C κ.B' = RatFunc.C B - 7 * RatFunc.C κ.w := by
    rw [B', map_sub, map_mul, map_ofNat]
  have hF : κ.FR = z * (-2 * Nn - 3 * M +
      (1 + RatFunc.C A * z ^ 2 + RatFunc.C B * z ^ 3) *
        (RatFunc.C κ.t + 2 * RatFunc.C κ.w * z + z ^ 2 * Nn) ^ 2 -
      2 * (RatFunc.C A + RatFunc.C B * z) * (RatFunc.C κ.t + 2 * RatFunc.C κ.w * z + z ^ 2 * Nn) -
      3 * (RatFunc.C κ.t + RatFunc.C κ.w * z + z ^ 2 * M) ^ 2 -
      z ^ 2 * (RatFunc.C κ.t + RatFunc.C κ.w * z + z ^ 2 * M) ^ 3 -
      (RatFunc.C A - 5 * RatFunc.C κ.t) * (RatFunc.C κ.t + RatFunc.C κ.w * z + z ^ 2 * M)) := by
    rw [FR, hXR, hXdR, psi_fpoly, hA', hB']
    exact infty_identity _ z M Nn _ _ _ _ hxz
  have hMO : M ∈ v.integer := by
    rw [hM]
    refine Subring.sum_mem _ fun Q _ => ?_
    have := heO Q
    have := hCO (tQ Q); have := hCO (uQ Q); have := hCO (xc Q)
    subring_mem
  have hNO : Nn ∈ v.integer := by
    rw [hNn]
    refine Subring.sum_mem _ fun Q _ => ?_
    have := heO Q
    have := hCO (tQ Q); have := hCO (uQ Q); have := hCO (xc Q)
    subring_mem
  rw [hF, map_mul]
  refine mul_lt_one_of_lt_of_le hvz ?_
  rw [← Valuation.mem_integer_iff]
  have := hCO A; have := hCO B; have := hCO κ.t; have := hCO κ.w
  subring_mem

/-- **The Vélu polynomial identity**:  in . -/
theorem Pv_eq_zero (h2 : (2 : K) ≠ 0) : κ.Pv = 0 := by
  classical
  have hdvd : κ.D ^ 6 ∣ κ.Pv := by
    rw [D, ← Finset.prod_pow]
    apply Finset.prod_dvd_of_coprime
    · intro Q hQ Q' hQ' hne
      exact IsCoprime.pow (isCoprime_X_sub_C_of_isUnit_sub
        (sub_ne_zero.2 (κ.xc_ne_of_mem_S hQ hQ' hne)).isUnit)
    · intro Q hQ; exact κ.local_dvd hQ h2
  obtain ⟨H, hH⟩ := hdvd
  have hF : κ.FR = ψ H := by
    have h := κ.psi_Pv
    rw [hH, map_mul, map_pow] at h
    exact (mul_left_cancel₀ (pow_ne_zero 6 κ.psi_D_ne) h).symm
  by_contra hne
  have hH0 : H ≠ 0 := by rintro rfl; exact hne (by simpa using hH)
  have hlt := κ.FR_val_lt
  rw [hF, RatFunc.inftyValuation_apply, RatFunc.inftyValuation.polynomial _ hH0,
    ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  omega

end Kernel

end Velu
