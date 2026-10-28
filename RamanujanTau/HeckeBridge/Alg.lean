import RamanujanTau.HeckeBridge.Univ

/-!
# `hAlg` of `HeckeQExp.classical_hU` for short curves

Over an algebraically closed field `K` of characteristic `0`:

* `IsQuotEnum p W Qs` — `W = short a b` is nonsingular and `Qs : Fin (p+1) → WeierstrassCurve K`
  lists the Vélu quotients `veluC G = E/G` of `E` by its order-`p` subgroups, each exactly once.
  (By `SubgroupSum.Kernel.curve_eq_veluC`, `veluC G` is the Vélu curve `κ.curve` of any Vélu
  kernel data `κ` with `κ.G = G`; such `κ` exists by `exists_kernel_of_mem_subs`, `p` odd.)
* `exists_quotEnum` — every nonsingular short curve has such an enumeration, with `Qs 0 = E/H₀`
  for any prescribed order-`p` subgroup `H₀` (`TorsionSpec.fullTorsion` + counting).
* **`hAlg_short`** — `Σ_c P(ptR(Qs c)) = (Siso p k P)(ptR W)`, `Siso p k P` isobaric of weight `k`.

The restriction to *short* Weierstrass models is harmless in characteristic `0` (in particular for
`p ≥ 5` residue characteristics): `ptR = (c₄, −c₆)` is a model invariant up to the scaling
`aeval_ptR_scale`, and every curve is isomorphic to a short one `y² = x³ − 27c₄x − 54c₆`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace HeckeBridge

open Velu SubgroupSum MvPolynomial ModP

variable {K : Type*} [Field K] [DecidableEq K] (p : ℕ) [hp : Fact p.Prime]

/-- `Qs` enumerates (bijectively) the Vélu quotients of the nonsingular short curve `W` by its
order-`p` subgroups. -/
def IsQuotEnum (W : WeierstrassCurve K) (Qs : Fin (p + 1) → WeierstrassCurve K) : Prop :=
  ∃ a b : K, 4 * a ^ 3 + 27 * b ^ 2 ≠ 0 ∧ W = (short a b : WeierstrassCurve K) ∧
    ∃ G : Fin (p + 1) → Finset (short a b).Point, (∀ c, G c ∈ subs a b p) ∧
      Function.Injective G ∧ (∀ H ∈ subs a b p, ∃ c, G c = H) ∧ ∀ c, Qs c = veluC (G c)

/-- **Existence of the quotient enumeration**, with a prescribed canonical quotient `Qs 0`. -/
theorem exists_quotEnum [IsAlgClosed K] [CharZero K] {a b : K} (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0)
    {H₀ : Finset (short a b).Point} (hH₀ : H₀ ∈ subs a b p) :
    ∃ Qs : Fin (p + 1) → WeierstrassCurve K, IsQuotEnum p (short a b) Qs ∧ Qs 0 = veluC H₀ := by
  obtain ⟨G, hmem, hinj, hsurj, h0⟩ := exists_enum_algClosed p hΔ hH₀
  exact ⟨fun c => veluC (G c), ⟨a, b, hΔ, rfl, G, hmem, hinj, hsurj, fun _ => rfl⟩, by simp only [h0]⟩

/-- Every nonsingular short curve has a quotient enumeration. -/
theorem exists_quotEnum' [IsAlgClosed K] [CharZero K] {a b : K} (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) :
    ∃ Qs : Fin (p + 1) → WeierstrassCurve K, IsQuotEnum p (short a b) Qs := by
  obtain ⟨H₀, hH₀⟩ := subs_nonempty p hΔ
  obtain ⟨Qs, h, -⟩ := exists_quotEnum p hΔ hH₀
  exact ⟨Qs, h⟩

/-- **`hAlg` for short curves**: the sum over the `p + 1` Vélu quotients of an isobaric `P` of
weight `k` is the isobaric weight-`k` polynomial `Siso p k P` evaluated at `ptR W`. -/
theorem hAlg_short [IsAlgClosed K] [CharZero K] {k : ℕ} {P : MvPolynomial (Fin 2) K} (hP : Iso P k)
    (W : WeierstrassCurve K) (Qs : Fin (p + 1) → WeierstrassCurve K) (hQ : IsQuotEnum p W Qs) :
    ∑ c, eval (HeckeQExp.ptR (Qs c)) P = eval (HeckeQExp.ptR W) (Siso p k P) := by
  obtain ⟨a, b, hΔ, rfl, G, hmem, hinj, hsurj, hQs⟩ := hQ
  simp only [hQs]
  have := subSum_Siso p (RingHom.id K) hP a b hΔ
  rw [map_id, map_id] at this
  rw [← this, ← sum_fin_eq_subSum _ G hmem hinj hsurj]
  rfl

/-- `hAlg` in exactly the shape of `HeckeQExp.classical_hU`, with `Good W := IsQuotEnum p W (Q W)`. -/
theorem hAlg [IsAlgClosed K] [CharZero K] {k : ℕ} {P : MvPolynomial (Fin 2) K} (hP : Iso P k)
    (Q : WeierstrassCurve K → Fin (p + 1) → WeierstrassCurve K) :
    ∀ W, IsQuotEnum p W (Q W) → ∑ c, eval (HeckeQExp.ptR (Q W c)) P =
      eval (HeckeQExp.ptR W) (Siso p k P) :=
  fun W hW => hAlg_short p hP W (Q W) hW

end HeckeBridge
