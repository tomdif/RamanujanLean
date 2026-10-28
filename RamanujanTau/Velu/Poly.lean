import RamanujanTau.Velu.JetSum
import RamanujanTau.Velu.Local
import RamanujanTau.Velu.LocalRing
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Vélu: the polynomial form of the identity and its local divisibility

Put `v_Q = X - x_Q`, `D = ∏_{Q∈S} v_Q`, `D_Q = D / v_Q`, and
`N = X D² + Σ (t_Q v_Q + u_Q) D_Q²`, `N₁ = D³ - Σ (t_Q v_Q + 2u_Q) D_Q³`,
so that `X = N/D²` and `X' = N₁/D³`. The Vélu identity is `Pv = 0` where
`Pv = f N₁² - N³ - A' N D⁴ - B' D⁶`, `f = X³ + AX + B`.

Main result here: `(X - x_{Q₀})⁶ ∣ Pv` for every `Q₀ ∈ S` (`local_dvd`): "no pole at `Q₀`".
-/

set_option linter.unusedSimpArgs false

namespace Velu

open Polynomial WeierstrassCurve

variable {K : Type*} [Field K] [DecidableEq K] {A B : K}

namespace Kernel

variable (κ : Kernel A B)

/-- `v_Q = X - x_Q`. -/
noncomputable def vp (Q : (short A B).Point) : K[X] := Polynomial.X - C (xc Q)

/-- `D = ∏_{Q∈S} (X - x_Q)`. -/
noncomputable def D : K[X] := ∏ Q ∈ κ.S, vp Q

/-- `D_Q = ∏_{Q'∈S, Q'≠Q} (X - x_{Q'})`. -/
noncomputable def Dq (Q : (short A B).Point) : K[X] := ∏ Q' ∈ κ.S.erase Q, vp Q'

/-- Numerator of Vélu's `X`: `X = N / D²`. -/
noncomputable def N : K[X] :=
  Polynomial.X * κ.D ^ 2 + ∑ Q ∈ κ.S, (C (tQ Q) * vp Q + C (uQ Q)) * κ.Dq Q ^ 2

/-- Numerator of `dX/dx`: `X' = N₁ / D³`. -/
noncomputable def N1 : K[X] :=
  κ.D ^ 3 - ∑ Q ∈ κ.S, (C (tQ Q) * vp Q + 2 * C (uQ Q)) * κ.Dq Q ^ 3

/-- `f = X³ + A X + B`. -/
noncomputable def fpoly (A B : K) : K[X] := Polynomial.X ^ 3 + C A * Polynomial.X + C B

/-- The Vélu polynomial `f N₁² - N³ - A' N D⁴ - B' D⁶` (`= D⁶ (f X'² - X³ - A'X - B')`). -/
noncomputable def Pv : K[X] :=
  fpoly A B * κ.N1 ^ 2 - κ.N ^ 3 - C κ.A' * κ.N * κ.D ^ 4 - C κ.B' * κ.D ^ 6

lemma D_eq {Q : (short A B).Point} (hQ : Q ∈ κ.S) : κ.D = vp Q * κ.Dq Q :=
  (Finset.mul_prod_erase _ _ hQ).symm

omit [DecidableEq K] in
lemma jet_zero_eq (δ t u : K) : jet 0 δ t u = t * δ⁻¹ + u * δ⁻¹ ^ 2 := by
  simp only [jet, div_eq_mul_inv, ← inv_pow]; push_cast; ring

omit [DecidableEq K] in
lemma jet_one_eq (δ t u : K) : jet 1 δ t u = -(t * δ⁻¹ ^ 2 + 2 * u * δ⁻¹ ^ 3) := by
  simp only [jet, div_eq_mul_inv, ← inv_pow]; push_cast; ring

omit [DecidableEq K] in
lemma jet_two_eq (δ t u : K) : jet 2 δ t u = t * δ⁻¹ ^ 3 + 3 * u * δ⁻¹ ^ 4 := by
  simp only [jet, div_eq_mul_inv, ← inv_pow]; push_cast; ring

omit [DecidableEq K] in
lemma jet_three_eq (δ t u : K) : jet 3 δ t u = -(t * δ⁻¹ ^ 4 + 4 * u * δ⁻¹ ^ 5) := by
  simp only [jet, div_eq_mul_inv, ← inv_pow]; push_cast; ring

omit [DecidableEq K] in
lemma sum_poly4 {ι 𝔸 : Type*} [CommRing 𝔸] (T : Finset ι) (c s : 𝔸) (a b d e : ι → 𝔸) :
    ∑ i ∈ T, c * (a i + b i * s + d i * s ^ 2 + e i * s ^ 3) =
      c * (∑ i ∈ T, a i + (∑ i ∈ T, b i) * s + (∑ i ∈ T, d i) * s ^ 2 +
        (∑ i ∈ T, e i) * s ^ 3) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih => simp only [Finset.sum_insert ha, ih]; ring

omit [DecidableEq K] in
lemma sum_poly3 {ι 𝔸 : Type*} [CommRing 𝔸] (T : Finset ι) (c s : 𝔸) (b d e : ι → 𝔸) :
    ∑ i ∈ T, c * (b i + 2 * d i * s + 3 * e i * s ^ 2) =
      c * (∑ i ∈ T, b i + 2 * (∑ i ∈ T, d i) * s + 3 * (∑ i ∈ T, e i) * s ^ 2) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih => simp only [Finset.sum_insert ha, ih]; ring

set_option maxHeartbeats 2000000 in
/-- **No pole at kernel points**: `(X - x_{Q₀})⁶ ∣ Pv` for `Q₀ ∈ S`. -/
theorem local_dvd {Q0 : (short A B).Point} (hQ0 : Q0 ∈ κ.S) (h2 : (2 : K) ≠ 0) :
    (Polynomial.X - C (xc Q0)) ^ 6 ∣ κ.Pv := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  set π := Ideal.Quotient.mk (Ideal.span {(Polynomial.X - C (xc Q0)) ^ 6}) with hπ
  set s := π (Polynomial.X - C (xc Q0)) with hs_def
  have hs : s ^ 6 = 0 := by
    rw [hs_def, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  set ι : K →+* _ := π.comp C with hι
  have hπC : ∀ c : K, π (C c) = ι c := fun c => rfl
  have hX : π Polynomial.X = ι (xc Q0) + s := by rw [hs_def, map_sub, hπC]; ring
  set E := π (κ.Dq Q0) with hE
  have hvQ0 : π (vp Q0) = s := rfl
  have hD : π κ.D = s * E := by rw [κ.D_eq hQ0, map_mul, hvQ0]
  -- data at the other points
  have hQdata : ∀ Q ∈ κ.S.erase Q0, π (vp Q) = ι (xc Q0 - xc Q) + s ∧
      ι (xc Q0 - xc Q) * ι ((xc Q0 - xc Q)⁻¹) = 1 := by
    intro Q hQ
    have hne : xc Q0 - xc Q ≠ 0 := sub_ne_zero.2
      (κ.xc_ne_of_mem_S hQ0 (Finset.mem_of_mem_erase hQ) (Finset.ne_of_mem_erase hQ).symm)
    refine ⟨?_, ?_⟩
    · rw [vp, map_sub, hπC, hX, map_sub]; ring
    · rw [← map_mul, mul_inv_cancel₀ hne, map_one]
  have hDq : ∀ Q ∈ κ.S.erase Q0,
      π (κ.Dq Q) = ivt (ι (xc Q0 - xc Q)⁻¹) s * s * E := by
    intro Q hQ
    obtain ⟨hv, hed⟩ := hQdata Q hQ
    have h1 := ivt_spec _ _ s hed hs
    have hDQ : π κ.D = π (vp Q) * π (κ.Dq Q) := by
      rw [κ.D_eq (Finset.mem_of_mem_erase hQ), map_mul]
    rw [hv] at hDQ
    calc π (κ.Dq Q) = ((ι (xc Q0 - xc Q) + s) * ivt (ι (xc Q0 - xc Q)⁻¹) s) * π (κ.Dq Q) := by
          rw [h1, one_mul]
      _ = ivt (ι (xc Q0 - xc Q)⁻¹) s * ((ι (xc Q0 - xc Q) + s) * π (κ.Dq Q)) := by ring
      _ = _ := by rw [← hDQ, hD]; ring
  -- the jets, mapped
  set jj : ℕ → (short A B).Point → K := fun k Q => jet k (xc Q0 - xc Q) (tQ Q) (uQ Q) with hjj
  have hNterm : ∀ Q ∈ κ.S.erase Q0,
      π ((C (tQ Q) * vp Q + C (uQ Q)) * κ.Dq Q ^ 2) =
        E ^ 2 * s ^ 2 * (ι (jj 0 Q) + ι (jj 1 Q) * s + ι (jj 2 Q) * s ^ 2 + ι (jj 3 Q) * s ^ 3) := by
    intro Q hQ
    obtain ⟨hv, hed⟩ := hQdata Q hQ
    rw [map_mul, map_add, map_mul, map_pow, hv, hDq Q hQ, hπC, hπC,
      N_term _ _ _ _ s E hed hs]
    simp only [hjj, jet_zero_eq, jet_one_eq, jet_two_eq, jet_three_eq, map_add, map_mul,
      map_pow, map_neg, map_ofNat]
  have hN1term : ∀ Q ∈ κ.S.erase Q0,
      π ((C (tQ Q) * vp Q + 2 * C (uQ Q)) * κ.Dq Q ^ 3) =
        -(E ^ 3 * s ^ 3 * (ι (jj 1 Q) + 2 * ι (jj 2 Q) * s + 3 * ι (jj 3 Q) * s ^ 2)) := by
    intro Q hQ
    obtain ⟨hv, hed⟩ := hQdata Q hQ
    rw [map_mul, map_add, map_mul, map_mul, map_pow, hv, hDq Q hQ, hπC, hπC, map_ofNat,
      N1_term _ _ _ _ s E hed hs]
    simp only [hjj, jet_zero_eq, jet_one_eq, jet_two_eq, jet_three_eq, map_add, map_mul,
      map_pow, map_neg, map_ofNat]
  -- assemble `π N` and `π N₁`
  have hN : π κ.N = E ^ 2 * (ι (tQ Q0) * s + ι (uQ Q0) +
      s ^ 2 * (ι (κ.Rj Q0 0) + ι (κ.Rj Q0 1) * s + ι (κ.Rj Q0 2) * s ^ 2 +
        ι (κ.Rj Q0 3) * s ^ 3)) := by
    rw [N, map_add, map_mul, map_pow, hX, hD, map_sum, ← Finset.add_sum_erase _ _ hQ0,
      Finset.sum_congr rfl hNterm, sum_poly4]
    simp only [map_add, map_mul, map_pow, hvQ0, ← hE, hπC]
    simp only [Rj, if_true, one_ne_zero, if_false, show (2:ℕ) ≠ 0 by decide,
      show (2:ℕ) ≠ 1 by decide, show (3:ℕ) ≠ 0 by decide, show (3:ℕ) ≠ 1 by decide,
      map_add, map_sum, map_one, map_zero, zero_add, hjj]
    ring
  have hN1 : π κ.N1 = E ^ 3 * (-(ι (tQ Q0) * s + 2 * ι (uQ Q0)) +
      s ^ 3 * (ι (κ.Rj Q0 1) + 2 * ι (κ.Rj Q0 2) * s + 3 * ι (κ.Rj Q0 3) * s ^ 2)) := by
    rw [N1, map_sub, map_pow, hD, map_sum, ← Finset.add_sum_erase _ _ hQ0,
      Finset.sum_congr rfl hN1term, Finset.sum_neg_distrib, sum_poly3]
    simp only [map_add, map_mul, map_pow, hvQ0, ← hE, hπC, map_ofNat]
    simp only [Rj, if_true, one_ne_zero, if_false, show (2:ℕ) ≠ 0 by decide,
      show (2:ℕ) ≠ 1 by decide, show (3:ℕ) ≠ 0 by decide, show (3:ℕ) ≠ 1 by decide,
      map_add, map_sum, map_one, map_zero, zero_add, hjj]
    ring
  have hf : π (fpoly A B) = ι (yc Q0) ^ 2 + (3 * ι (xc Q0) ^ 2 + ι A) * s +
      3 * ι (xc Q0) * s ^ 2 + s ^ 3 := by
    have hc := congrArg ι (equation_xc_yc (κ.ne_zero_of_mem_S hQ0))
    simp only [map_add, map_mul, map_pow] at hc
    rw [fpoly, map_add, map_add, map_mul, map_pow, hX, hπC, hπC, hc]
    ring
  -- the scalar identities, mapped
  have hy0 : yc Q0 ≠ 0 := κ.yc_ne_zero hQ0
  obtain ⟨hx2, hy2⟩ := double_coords (κ.ne_zero_of_mem_S hQ0) hy0 h2
  obtain ⟨k2, k3, k4, k5⟩ := local_scalar_identities (xc Q0) (yc Q0) A κ.t
    (κ.Rj Q0 0) (κ.Rj Q0 1) (κ.Rj Q0 2) (κ.Rj Q0 3) (xc (Q0 + Q0)) (yc (Q0 + Q0)) hy0 h2
    hx2 hy2 (Rj_zero hQ0 h2) (Rj_one hQ0 h2) (Rj_two hQ0 h2) (Rj_three hQ0 h2)
  have m2 := congrArg ι k2
  have m3 := congrArg ι k3
  have m4 := congrArg ι k4
  have m5 := congrArg ι k5
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero] at m2 m3 m4 m5
  have key := local_vanish (ι (xc Q0)) (ι (yc Q0)) (ι A) (ι κ.t) (ι (κ.Rj Q0 0))
    (ι (κ.Rj Q0 1)) (ι (κ.Rj Q0 2)) (ι (κ.Rj Q0 3)) (ι κ.B') s hs
    (by linear_combination m2) (by linear_combination m3) (by linear_combination m4)
    (by linear_combination m5)
  have hA' : ι κ.A' = ι A - 5 * ι κ.t := by rw [A', map_sub, map_mul, map_ofNat]
  rw [Pv, map_sub, map_sub, map_sub, map_mul, map_mul, map_mul, map_mul, map_pow, map_pow,
    map_pow, map_pow, hπC, hπC, hA', hN, hN1, hD, hf]
  simp only [tQ, uQ, map_add, map_mul, map_pow, map_ofNat]
  linear_combination E ^ 6 * key

end Kernel

end Velu
