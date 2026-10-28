/-
# Atkin–O'Brien: from matrix bounds (UB)/(DB) to the envelope hypothesis `hT`

Katz coordinates are modelled as `f : ℕ → M` (the component of `f` in `B_j`), and an operator by its blocks
`T i j : M →ₗ M`, so that `(T f)_i = Σ_{j<n} T i j (f j)`. A matrix bound `mat i j` says that `T i j`
raises `ϖ`-divisibility by `mat i j`, which may be negative (`pU` is integral, not `U`). Divisibility
by `ϖ^a` with `a : ℤ` means divisibility by `ϖ^{a.toNat}`. The ultrametric inequality is then just
"a sum of multiples of `ϖ^e` is a multiple of `ϖ^e`".
-/
import RamanujanTau.AtkinOBrien.Envelope
import RamanujanTau.AtkinOBrien.Induction

set_option autoImplicit false

namespace AtkinOBrien

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

lemma Dvd.mono {ϖ : R} {a b : ℕ} {x : M} (hab : a ≤ b) (h : Dvd ϖ b x) : Dvd ϖ a x := by
  obtain ⟨y, rfl⟩ := h
  exact ⟨ϖ ^ (b - a) • y, by rw [← mul_smul, ← pow_add, Nat.add_sub_cancel' hab]⟩

lemma Dvd.sum {ϖ : R} {e : ℕ} (s : Finset ℕ) (g : ℕ → M) (h : ∀ j ∈ s, Dvd ϖ e (g j)) :
    Dvd ϖ e (∑ j ∈ s, g j) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    obtain ⟨y, hy⟩ := h a (Finset.mem_insert_self _ _)
    obtain ⟨z, hz⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    exact ⟨y + z, by rw [smul_add, ← hy, ← hz]⟩

/-- **generic bridge**: if `out i ≤ max 0 (lo j) + mat i j` for all `i, j`, then every `f` whose
`j`-th coordinate is divisible by `ϖ^{max 0 (lo j)}` is sent to a form whose `i`-th coordinate is divisible
by `ϖ^{out i}`. -/
theorem bridge (ϖ : R) (n : ℕ) (T : ℕ → ℕ → M →ₗ[R] M) (lo out : ℕ → ℤ) (mat : ℕ → ℕ → ℤ)
    (henv : ∀ i j, out i ≤ max 0 (lo j) + mat i j)
    (hmat : ∀ i j (a : ℕ) (x : M), Dvd ϖ a x → Dvd ϖ ((a : ℤ) + mat i j).toNat (T i j x))
    (f : ℕ → M) (hf : ∀ j, Dvd ϖ (max 0 (lo j)).toNat (f j)) (i : ℕ) :
    Dvd ϖ (out i).toNat (∑ j ∈ Finset.range n, T i j (f j)) := by
  refine Dvd.sum _ _ fun j _ => ?_
  have h := hmat i j _ _ (hf j)
  refine Dvd.mono ?_ h
  have := henv i j
  have h0 : ((max 0 (lo j)).toNat : ℤ) = max 0 (lo j) := Int.toNat_of_nonneg (le_max_left _ _)
  omega

/-- **(UB) ⇒ `U(A_c(β)) ⊆ A_1(α)`** coordinatewise, for `p ≥ 13` and `c ≤ 2`. -/
theorem U_maps (p : ℕ) (hp : 13 ≤ p) (c : ℤ) (hc : c ≤ 2) (ϖ : R) (n : ℕ) (U : ℕ → ℕ → M →ₗ[R] M)
    (hUB : ∀ i j (a : ℕ) (x : M), Dvd ϖ a x → Dvd ϖ ((a : ℤ) + u p i j).toNat (U i j x))
    (f : ℕ → M) (hf : ∀ j, Dvd ϖ (max 0 (β p j - c)).toNat (f j)) (i : ℕ) :
    Dvd ϖ (α p i - 1).toNat (∑ j ∈ Finset.range n, U i j (f j)) :=
  bridge ϖ n U (fun j => β p j - c) (fun i => α p i - 1) (u p) (U_step hp c hc) hUB f hf i

/-- **(DB) ⇒ `D(A_c(α)) ⊆ A_1(β)`** coordinatewise, for `p ≥ 13` and `c ≤ 2`. -/
theorem D_maps (p : ℕ) (hp : 13 ≤ p) (c : ℤ) (hc : c ≤ 2) (ϖ : R) (n : ℕ) (D : ℕ → ℕ → M →ₗ[R] M)
    (hDB : ∀ i j (a : ℕ) (x : M), Dvd ϖ a x → Dvd ϖ ((a : ℤ) + d p i j).toNat (D i j x))
    (f : ℕ → M) (hf : ∀ j, Dvd ϖ (max 0 (α p j - c)).toNat (f j)) (i : ℕ) :
    Dvd ϖ (β p i - 1).toNat (∑ j ∈ Finset.range n, D i j (f j)) :=
  bridge ϖ n D (fun j => α p j - c) (fun i => β p i - 1) (d p) (D_step hp c hc) hDB f hf i

end AtkinOBrien
