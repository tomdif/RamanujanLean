import RamanujanTau.Velu.OfSubgroup
import RamanujanTau.HeckeQExp.Geom

/-!
# Subgroup sums: intrinsic Vélu coefficients

For a short curve `E : y² = x³ + A x + B` over a field `K` and a finite set `G` of points
(typically a subgroup), put
* `tSum G = Σ_{P ∈ G ∖ 0} (6 x_P² + 2A)`,
* `wSum G = Σ_{P ∈ G ∖ 0} (4 y_P² + x_P (6 x_P² + 2A))`,
* `aC G = A − 5·tSum G / 2`, `bC G = B − 7·wSum G / 2`, `veluC G = short (aC G) (bC G)`.

These depend only on `G`, not on a choice of representatives of `(G ∖ 0)/±`:
`Kernel.A'_eq_aC`, `Kernel.B'_eq_bC`, `Kernel.curve_eq_veluC` (char `≠ 2`).

* `subs A B n` — the finite subsets of `E(K)` that are subgroups of cardinality `n`.
* `subSum n f A B = Σ_{G ∈ subs A B n} f (aC G) (bC G)` — the subgroup sum.
* `exists_kernel_of_mem_subs` — every `G ∈ subs A B n`, `n` odd, is `κ.G` for Vélu kernel data `κ`.
* `ptR_veluC` — `(c₄, −c₆)` of `veluC G` is `(−48·aC G, 864·bC G)`.
-/

set_option autoImplicit false

namespace SubgroupSum

open Velu WeierstrassCurve

variable {K : Type*} [Field K] [DecidableEq K] {A B : K}

/-- `Σ_{P ∈ G ∖ 0} t_P`. -/
def tSum (G : Finset (short A B).Point) : K := ∑ P ∈ G.erase 0, Kernel.tQ (A := A) (B := B) P

/-- `Σ_{P ∈ G ∖ 0} (u_P + x_P t_P)`. -/
def wSum (G : Finset (short A B).Point) : K :=
  ∑ P ∈ G.erase 0, (Kernel.uQ (A := A) (B := B) P + xc P * Kernel.tQ (A := A) (B := B) P)

/-- The intrinsic Vélu coefficient `A' = A − 5·tSum/2`. -/
def aC (G : Finset (short A B).Point) : K := A - 5 * tSum G / 2

/-- The intrinsic Vélu coefficient `B' = B − 7·wSum/2`. -/
def bC (G : Finset (short A B).Point) : K := B - 7 * wSum G / 2

/-- The Vélu quotient curve attached to `G`. -/
def veluC (G : Finset (short A B).Point) : WeierstrassCurve K := short (aC G) (bC G)

omit [DecidableEq K] in
/-- `(c₄, −c₆)` of a short curve. -/
lemma ptR_short (a b : K) : HeckeQExp.ptR (short a b : WeierstrassCurve K) = ![-48 * a, 864 * b] := by
  funext i; fin_cases i
  · simp [HeckeQExp.ptR, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]; ring
  · simp [HeckeQExp.ptR, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆]; ring

lemma ptR_veluC (G : Finset (short A B).Point) :
    HeckeQExp.ptR (veluC G) = ![-48 * aC G, 864 * bC G] := ptR_short _ _

/-! ### Independence of the choice of representatives -/

section Kernel

/-- For an even function `f` on points, `Σ_{G∖0} f = 2 Σ_S f`. -/
lemma sum_erase_zero_eq_two_mul (κ : Kernel A B) (f : (short A B).Point → K)
    (hf : ∀ P, f (-P) = f P) : ∑ P ∈ κ.G.erase 0, f P = 2 * ∑ P ∈ κ.S, f P := by
  classical
  have hinj : Set.InjOn (fun P : (short A B).Point => -P) (κ.S : Set _) :=
    fun P _ Q _ h => neg_injective h
  have hdisj : Disjoint κ.S (κ.S.image fun P => -P) := by
    rw [Finset.disjoint_left]
    intro P hP hP'
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 hP'
    exact κ.neg_not_mem_S Q hQ hP
  have hG : κ.G.erase 0 = κ.S ∪ κ.S.image fun P => -P := by
    ext P
    simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨h0, hP⟩
      rcases κ.cover P hP h0 with h | h
      · exact Or.inl h
      · exact Or.inr ⟨-P, h, neg_neg P⟩
    · rintro (h | ⟨Q, hQ, rfl⟩)
      · exact ⟨fun h' => κ.zero_not_mem_S (h' ▸ h), κ.S_sub h⟩
      · refine ⟨fun h' => κ.zero_not_mem_S ?_, κ.neg_mem Q (κ.S_sub hQ)⟩
        rw [neg_eq_zero] at h'; exact h' ▸ hQ
  rw [hG, Finset.sum_union hdisj, Finset.sum_image hinj]
  simp only [hf]; ring

lemma two_mul_t (κ : Kernel A B) : 2 * κ.t = tSum κ.G := by
  rw [tSum, sum_erase_zero_eq_two_mul κ _ (fun P => by simp [Kernel.tQ]), Kernel.t]

lemma two_mul_w (κ : Kernel A B) : 2 * κ.w = wSum κ.G := by
  rw [wSum, sum_erase_zero_eq_two_mul κ _ (fun P => by simp [Kernel.tQ, Kernel.uQ]), Kernel.w]

theorem Kernel.A'_eq_aC (h2 : (2 : K) ≠ 0) (κ : Kernel A B) : κ.A' = aC κ.G := by
  rw [Kernel.A', aC, ← two_mul_t]; field_simp

theorem Kernel.B'_eq_bC (h2 : (2 : K) ≠ 0) (κ : Kernel A B) : κ.B' = bC κ.G := by
  rw [Kernel.B', bC, ← two_mul_w]; field_simp

theorem Kernel.curve_eq_veluC (h2 : (2 : K) ≠ 0) (κ : Kernel A B) :
    (κ.curve : WeierstrassCurve K) = veluC κ.G := by
  rw [Kernel.curve, veluC, Kernel.A'_eq_aC h2, Kernel.B'_eq_bC h2]

end Kernel

/-! ### Finite subgroups of a given order -/

/-- `G` is closed under `0`, `+`, `-`. -/
def IsSub (G : Finset (short A B).Point) : Prop :=
  0 ∈ G ∧ (∀ P ∈ G, ∀ Q ∈ G, P + Q ∈ G) ∧ ∀ P ∈ G, -P ∈ G

/-- The finite subgroups of `E(K)` of cardinality `n`. -/
def subs (A B : K) (n : ℕ) : Set (Finset (short A B).Point) := {G | IsSub G ∧ G.card = n}

/-- **The subgroup sum** `Σ_{|G| = n} f(A'_G, B'_G)` (defined as `0` if there were infinitely many
such subgroups; over a field there are not, but this is not needed here). -/
noncomputable def subSum (n : ℕ) (f : K → K → K) (A B : K) : K := by
  classical exact
  if h : (subs A B n).Finite then ∑ G ∈ h.toFinset, f (aC G) (bC G) else 0

/-- The additive subgroup of a finite set closed under the group operations. -/
def IsSub.toAddSubgroup {G : Finset (short A B).Point} (hG : IsSub G) :
    AddSubgroup (short A B).Point where
  carrier := G
  zero_mem' := hG.1
  add_mem' := fun ha hb => hG.2.1 _ ha _ hb
  neg_mem' := fun ha => hG.2.2 _ ha

/-- Every finite subgroup of odd order is the `G` of some Vélu kernel data. -/
theorem exists_kernel_of_mem_subs {n : ℕ} (hn : Odd n) {G : Finset (short A B).Point}
    (hG : G ∈ subs A B n) : ∃ κ : Kernel A B, κ.G = G := by
  obtain ⟨hS, hc⟩ := hG
  have hfin : Finite hS.toAddSubgroup := (G.finite_toSet).to_subtype
  have hcard : Nat.card hS.toAddSubgroup = G.card := by
    change Nat.card (G : Set (short A B).Point) = G.card
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
  obtain ⟨κ, hκ⟩ := exists_kernel hS.toAddSubgroup (by rw [hcard, hc]; exact hn)
  exact ⟨κ, Finset.coe_injective hκ⟩

end SubgroupSum
