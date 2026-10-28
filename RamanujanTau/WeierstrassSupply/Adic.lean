/-
# `integers K` is `π`-adically complete

For a complete ultrametric normed field `K` and `π ∈ 𝒪 = integers K` with `0 < ‖π‖ < 1`, the ring `𝒪` is
`(π)`-adically complete: `(π)^n = {x | ‖x‖ ≤ ‖π‖^n}`.
-/
import RamanujanTau.CanonicalIsogeny.Integers

set_option autoImplicit false

namespace WeierstrassSupply
open CanonicalIsogeny

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "𝒪" => integers K

lemma dvd_iff_norm_le {π x : 𝒪} (hπ : π ≠ 0) : π ∣ x ↔ ‖(x : K)‖ ≤ ‖(π : K)‖ := by
  have hπK : (π : K) ≠ 0 := fun h => hπ (Subtype.ext h)
  constructor
  · rintro ⟨c, rfl⟩
    rw [Subring.coe_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) c.2
  · intro h
    refine ⟨⟨(x : K) / π, ?_⟩, Subtype.ext ?_⟩
    · rw [mem_integers, norm_div]
      exact div_le_one_of_le₀ h (norm_nonneg _)
    · rw [Subring.coe_mul]; field_simp

lemma mem_pow_smul_top_iff {π : 𝒪} (hπ : π ≠ 0) (n : ℕ) (x : 𝒪) :
    x ∈ ((Ideal.span {π}) ^ n • ⊤ : Submodule 𝒪 𝒪) ↔ ‖(x : K)‖ ≤ ‖(π : K)‖ ^ n := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    dvd_iff_norm_le (pow_ne_zero n hπ), Subring.coe_pow, norm_pow]

lemma smodEq_iff {π : 𝒪} (hπ : π ≠ 0) (n : ℕ) (x y : 𝒪) :
    x ≡ y [SMOD ((Ideal.span {π}) ^ n • ⊤ : Submodule 𝒪 𝒪)] ↔ ‖(x : K) - y‖ ≤ ‖(π : K)‖ ^ n := by
  rw [SModEq.sub_mem, mem_pow_smul_top_iff hπ]; rfl

theorem isAdicComplete [CompleteSpace K] {π : 𝒪} (hπ0 : π ≠ 0) (hπ1 : ‖(π : K)‖ < 1) :
    IsAdicComplete (Ideal.span {π}) 𝒪 := by
  have hlim : Filter.Tendsto (fun n : ℕ => ‖(π : K)‖ ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hπ1
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have hx' : ∀ n : ℕ, ‖(x : K)‖ ≤ ‖(π : K)‖ ^ n := fun n => by
      simpa using (smodEq_iff hπ0 n x 0).mp (hx n)
    have : ‖(x : K)‖ ≤ 0 := ge_of_tendsto' hlim hx'
    exact Subtype.ext (by simpa using le_antisymm this (norm_nonneg _))
  · intro f hf
    have hf' : ∀ {m n}, m ≤ n → ‖(f m : K) - f n‖ ≤ ‖(π : K)‖ ^ m := fun {m n} h =>
      (smodEq_iff hπ0 m _ _).mp (hf h)
    have hc : CauchySeq f := by
      refine cauchySeq_of_le_geometric ‖(π : K)‖ 1 hπ1 fun n => ?_
      rw [one_mul, dist_eq_norm]; exact hf' (Nat.le_succ n)
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    refine ⟨L, fun n => (smodEq_iff hπ0 n _ _).mpr ?_⟩
    have hL' : Filter.Tendsto (fun m => ‖(f n : K) - (f m : K)‖) Filter.atTop (nhds ‖(f n : K) - L‖) :=
      ((continuous_subtype_val.tendsto L).comp hL).const_sub _ |>.norm
    exact le_of_tendsto hL' (Filter.eventually_atTop.mpr ⟨n, fun m hm => hf' hm⟩)

end WeierstrassSupply
