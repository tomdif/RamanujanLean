/-
# Atkin–O'Brien for ℓ ∈ {13,17,19,23}: the induction (Step 3) and the η-identity (Step 1)

`docs/ATKIN_OBRIEN_PROOF.md`, Step 3, as an abstract theorem. The analytic inputs are explicit hypotheses:
* `R` is a ring in which every element is a unit or divisible by `ϖ` (e.g. `ℤ_ℓ`, `ϖ = ℓ`);
* `M` is `ϖ`-torsion-free (weight-0 overconvergent forms with integral Katz expansions);
* `A₁ b, A₂ b` are the offset-1/offset-2 envelopes, `T b` is `U` or `D` according to the parity of `b`.
The hypotheses are:
* `hT` — Step 2(1);
* `hlead` — a form in `A₁` is, mod `ϖ`, a multiple of `L b` (this is `dim S_{ℓ−1} = 1`, plus `L b ≢ 0`);
* `hdiv` — Katz-expansion uniqueness;
* `hbase`, `hstab` — Boylan–Webb (`b_ℓ(1) = 1` and stability at *some* finite level);
* `hnz` — `L b ≢ 0 (mod ϖ)`.
The conclusion is the sharp threshold `L(b+2) ≡ κ L(b) (mod ϖ^b)`.
-/
import Mathlib

set_option autoImplicit false

namespace AtkinOBrien

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- `x ≡ 0 (mod ϖ^m)`. -/
def Dvd (ϖ : R) (m : ℕ) (x : M) : Prop := ∃ y : M, x = ϖ ^ m • y

lemma cancel_pow (ϖ : R) (hreg : ∀ x : M, ϖ • x = 0 → x = 0) (m : ℕ) (x : M) (h : ϖ ^ m • x = 0) : x = 0 := by
  induction m generalizing x with
  | zero => simpa using h
  | succ m ih => exact hreg x (ih _ (by rw [← mul_smul, ← pow_succ]; exact h))

theorem induction (ϖ κ : R) (T : ℕ → M →ₗ[R] M) (L : ℕ → M) (A₁ A₂ : ℕ → Submodule R M)
    (hR : ∀ c : R, IsUnit c ∨ ∃ d, c = ϖ * d)
    (hreg : ∀ x : M, ϖ • x = 0 → x = 0)
    (hTper : ∀ b, T (b + 2) = T b) (hLT : ∀ b, L (b + 1) = T b (L b))
    (hA₁per : ∀ b, A₁ (b + 2) = A₁ b) (hL : ∀ b, 1 ≤ b → L b ∈ A₁ b)
    (hT : ∀ b, 1 ≤ b → ∀ x ∈ A₂ b, T b x ∈ A₁ (b + 1))
    (hlead : ∀ b, 1 ≤ b → ∀ x ∈ A₁ b, ∃ c : R, ∃ y : M, x = c • L b + ϖ • y)
    (hdiv : ∀ b, 1 ≤ b → ∀ x ∈ A₁ b, ∀ y : M, x = ϖ • y → y ∈ A₂ b)
    (hnz : ∀ b, 1 ≤ b → ¬ ∃ y : M, L b = ϖ • y)
    (hbase : Dvd ϖ 1 (L 3 - κ • L 1))
    (hstab : ∀ m, ∃ N, ∀ b ≥ N, Dvd ϖ m (L (b + 2) - κ • L b)) :
    ∀ b, 1 ≤ b → Dvd ϖ b (L (b + 2) - κ • L b) := by
  set e : ℕ → M := fun b => L (b + 2) - κ • L b with he_def
  have he : ∀ b, e (b + 1) = T b (e b) := by
    intro b
    show L (b + 2 + 1) - κ • L (b + 1) = T b (L (b + 2) - κ • L b)
    rw [map_sub, map_smul, hLT (b + 2), hTper, hLT b]
  -- strengthened claim: `e b = ϖ^b • g` with `g ∈ A₂ b`
  have key : ∀ b, 1 ≤ b → ∃ g ∈ A₂ b, e b = ϖ ^ b • g := by
    intro b hb
    induction b, hb using Nat.le_induction with
    | base =>
      obtain ⟨y, hy⟩ := hbase
      have hmem : e 1 ∈ A₁ 1 := by
        have h3 : L 3 ∈ A₁ 1 := by rw [← hA₁per 1]; exact hL 3 (by norm_num)
        exact Submodule.sub_mem _ h3 (Submodule.smul_mem _ _ (hL 1 le_rfl))
      rw [pow_one] at hy
      exact ⟨y, hdiv 1 le_rfl _ hmem y hy, by rw [pow_one]; exact hy⟩
    | succ b hb ih =>
      obtain ⟨g, hg, hge⟩ := ih
      have hx : T b g ∈ A₁ (b + 1) := hT b hb g hg
      obtain ⟨c, h, hch⟩ := hlead (b + 1) (by omega) _ hx
      -- propagate: `e β = ϖ^b c L β + ϖ^(b+1) z` for all `β ≥ b+1`
      have prop : ∀ k, ∃ z : M, e (b + 1 + k) = ϖ ^ b • c • L (b + 1 + k) + ϖ ^ (b + 1) • z := by
        intro k
        induction k with
        | zero =>
          refine ⟨h, ?_⟩
          rw [Nat.add_zero, he, hge, map_smul, hch, smul_add, pow_succ, mul_smul]
        | succ k ihk =>
          obtain ⟨z, hz⟩ := ihk
          refine ⟨T (b + 1 + k) z, ?_⟩
          rw [show b + 1 + (k + 1) = b + 1 + k + 1 by omega, he, hz, map_add, map_smul, map_smul, map_smul,
            ← hLT]
      obtain ⟨N, hN⟩ := hstab (b + 1)
      obtain ⟨z, hz⟩ := prop N
      obtain ⟨y, hy⟩ := hN (b + 1 + N) (by omega)
      have hcL : c • L (b + 1 + N) = ϖ • (y - z) := by
        have h0 : ϖ ^ b • (c • L (b + 1 + N) - ϖ • (y - z)) = 0 := by
          have : e (b + 1 + N) = ϖ ^ (b + 1) • y := hy
          rw [hz] at this
          simp only [smul_sub, ← mul_smul, ← pow_succ] at this ⊢
          rw [← sub_eq_zero] at this
          rw [← this]; abel
        exact sub_eq_zero.mp (cancel_pow ϖ hreg b _ h0)
      obtain ⟨d, rfl⟩ : ∃ d, c = ϖ * d := by
        rcases hR c with ⟨u, rfl⟩ | hd
        · exfalso
          apply hnz (b + 1 + N) (by omega)
          refine ⟨(↑u⁻¹ : R) • (y - z), ?_⟩
          rw [smul_comm, ← hcL, ← mul_smul, Units.inv_mul, one_smul]
        · exact hd
      refine ⟨d • L (b + 1) + h, hdiv (b + 1) (by omega) _ hx _ (by rw [hch, smul_add, mul_smul]), ?_⟩
      rw [he, hge, map_smul, hch, mul_smul, ← smul_add, ← mul_smul, ← pow_succ]
  intro b hb
  obtain ⟨g, -, hg⟩ := key b hb
  exact ⟨g, hg⟩

/-- **Step 1's exact identity** `(E^s W)² = Q^p · V(Q) · G`, with `2s = p+1`, `W = V²P/P^{p²}`,
`Q = E·(VP)²/P^{2p}`, `G = E/V(E)`. It holds in any commutative group with an endomorphism `V`; in the
application, `P = (q;q)_∞`, `V = (q ↦ q^p)`, and `E = E_{p−1}`, all units of `ℤ⟦q⟧`. -/
theorem eta_identity {G : Type*} [CommGroup G] (V : G →* G) (P E : G) (p s : ℕ) (hs : 2 * s = p + 1) :
    (E ^ s * (V (V P) * (P ^ (p ^ 2))⁻¹)) ^ 2 =
      (E * V P ^ 2 * (P ^ (2 * p))⁻¹) ^ p * V (E * V P ^ 2 * (P ^ (2 * p))⁻¹) * (E * (V E)⁻¹) := by
  rw [mul_pow, ← pow_mul, mul_comm s 2, hs]
  apply Additive.ofMul.injective
  simp only [map_mul, map_inv, map_pow, ofMul_mul, ofMul_pow, ofMul_inv]
  module

end AtkinOBrien
