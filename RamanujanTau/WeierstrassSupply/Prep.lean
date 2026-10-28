/-
# Weierstrass preparation over `integers K` (norm form)

`K` a complete ultrametric normed field (not necessarily discretely valued), `𝒪 = integers K`.
If `g ∈ 𝒪⟦T⟧` has `‖g_k‖ ≤ ‖π‖ < 1` for `k < N` (some `π ≠ 0`) and `‖g_N‖ = 1`, then `g = P·U` with
`P ∈ 𝒪[X]` monic of degree `N` and `U ∈ 𝒪⟦T⟧ˣ`. Proof: `𝒪` is `(π)`-adically complete (`Adic.lean`), so
Mathlib's Weierstrass division by `g` at the ideal `(π)` applies to `T^N = g q + r`; the coefficient of
`T^N` shows `‖q₀‖ = 1`.
-/
import RamanujanTau.WeierstrassSupply.Adic

set_option autoImplicit false

namespace WeierstrassSupply
open CanonicalIsogeny

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "𝒪" => integers K

lemma isUnit_of_norm_eq_one {x : 𝒪} (hx : ‖(x : K)‖ = 1) : IsUnit x := by
  have hx0 : (x : K) ≠ 0 := by intro h; rw [h, norm_zero] at hx; exact zero_ne_one hx
  have hm : (x : K)⁻¹ ∈ integers K := by rw [mem_integers, norm_inv, hx, inv_one]
  exact IsUnit.of_mul_eq_one (b := ⟨(x : K)⁻¹, hm⟩)
    (Subtype.ext (by rw [Subring.coe_mul]; exact mul_inv_cancel₀ hx0))

lemma norm_eq_one_of_isUnit {x : 𝒪} (hx : IsUnit x) : ‖(x : K)‖ = 1 := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  have h := congrArg (fun z : 𝒪 => ‖(z : K)‖) hy
  simp only [Subring.coe_mul, norm_mul, OneMemClass.coe_one, norm_one] at h
  have h1 : ‖(x : K)‖ ≤ 1 := x.2
  have h2 : ‖(y : K)‖ ≤ 1 := y.2
  nlinarith [norm_nonneg (x : K), norm_nonneg (y : K)]

theorem exists_prep [CompleteSpace K] (g : PowerSeries 𝒪) (N : ℕ) (π : 𝒪) (hπ0 : π ≠ 0)
    (hπ1 : ‖(π : K)‖ < 1) (hlow : ∀ k < N, ‖((PowerSeries.coeff k g : 𝒪) : K)‖ ≤ ‖(π : K)‖)
    (hN : ‖((PowerSeries.coeff N g : 𝒪) : K)‖ = 1) :
    ∃ (P : Polynomial 𝒪) (U : PowerSeries 𝒪), P.Monic ∧ P.natDegree = N ∧ IsUnit U ∧
      g = (P : PowerSeries 𝒪) * U := by
  haveI := isAdicComplete hπ0 hπ1
  set I := Ideal.span {π}
  have hord : (g.map (Ideal.Quotient.mk I)).order = N := by
    rw [PowerSeries.order_eq_nat]
    refine ⟨?_, fun i hi => ?_⟩
    · rw [PowerSeries.coeff_map, ne_eq, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
        dvd_iff_norm_le hπ0, hN]
      exact not_le.mpr hπ1
    · rw [PowerSeries.coeff_map, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
        dvd_iff_norm_le hπ0]
      exact hlow i hi
  have hNt : (g.map (Ideal.Quotient.mk I)).order.toNat = N := by rw [hord]; rfl
  have hD : g.IsWeierstrassDivisorAt I := by
    unfold PowerSeries.IsWeierstrassDivisorAt; rw [hNt]; exact isUnit_of_norm_eq_one hN
  have H := hD.isWeierstrassDivisionAt_div_mod (PowerSeries.X ^ N)
  set q := hD.div (PowerSeries.X ^ N)
  set r := hD.mod (PowerSeries.X ^ N)
  have hdeg : r.degree < N := by have := H.degree_lt; rwa [hNt] at this
  have heq : PowerSeries.X ^ N = g * q + (r : PowerSeries 𝒪) := H.eq_mul_add
  -- `q` is a unit
  have hq : IsUnit q := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    apply isUnit_of_norm_eq_one
    have hc := congrArg (PowerSeries.coeff N) heq
    rw [PowerSeries.coeff_X_pow_self, map_add, Polynomial.coeff_coe,
      Polynomial.coeff_eq_zero_of_degree_lt hdeg, add_zero, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => PowerSeries.coeff i g * PowerSeries.coeff j q),
      Finset.sum_range_succ, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply] at hc
    have hcK := congrArg (fun z : 𝒪 => (z : K)) hc
    simp only [OneMemClass.coe_one, Subring.coe_add, Subring.coe_mul] at hcK
    set S := ∑ x ∈ Finset.range N, PowerSeries.coeff x g * PowerSeries.coeff (N - x) q with hS
    have hs : ‖(S : K)‖ ≤ ‖(π : K)‖ := by
      show ‖incl S‖ ≤ _
      rw [hS, map_sum]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun k hk => ?_
      rw [map_mul, norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (PowerSeries.coeff (N - k) q).2).trans
        (hlow k (Finset.mem_range.mp hk))
    have h0 : ‖((PowerSeries.constantCoeff q : 𝒪) : K)‖ ≤ 1 := (PowerSeries.constantCoeff q).2
    by_contra hne
    have hlt : ‖((PowerSeries.constantCoeff q : 𝒪) : K)‖ < 1 := lt_of_le_of_ne h0 hne
    have h1 : ‖((PowerSeries.coeff N g : 𝒪) : K) * ((PowerSeries.constantCoeff q : 𝒪) : K)‖ < 1 := by
      rw [norm_mul, hN, one_mul]; exact hlt
    have := congrArg norm hcK
    rw [norm_one] at this
    have h2 := IsUltrametricDist.norm_add_le_max (S : K)
      (((PowerSeries.coeff N g : 𝒪) : K) * ((PowerSeries.constantCoeff q : 𝒪) : K))
    rw [← this] at h2
    have := max_lt (hs.trans_lt hπ1) h1
    linarith
  refine ⟨Polynomial.X ^ N - r, ↑hq.unit⁻¹, Polynomial.monic_X_pow_sub hdeg, ?_, Units.isUnit _, ?_⟩
  · apply Polynomial.natDegree_eq_of_degree_eq_some
    rw [Polynomial.degree_sub_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]),
      Polynomial.degree_X_pow]
  · have h1 : g * q = (((Polynomial.X ^ N - r : Polynomial 𝒪)) : PowerSeries 𝒪) := by
      rw [Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X, heq]; ring
    rw [← h1, mul_assoc, IsUnit.mul_val_inv, mul_one]

end WeierstrassSupply
