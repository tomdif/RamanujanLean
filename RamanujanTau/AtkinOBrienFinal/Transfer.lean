import RamanujanTau.AtkinOBrienFinal.Katz
import RamanujanTau.AtkinOBrien.Bridge
import RamanujanTau.BoylanWebb.Series

/-!
# The matrix bounds (UB), (DB) and the envelope map `hT`

**(UB)** (`UB ℓ hℓ`): for every Katz index `j` and every integral `b ∈ B_j`, `U(b/E^j)` has an (integral)
Katz expansion `Σ_i c_i/E^i` with `v_i(c_i) ≥ u(i,j) = ⌈(ℓi − j)/(ℓ+1)⌉ − 1`.

**(DB)** (`DB ℓ hℓ`): the same for `D(b/E^j) = U(Φ·b/E^j)`, `Φ = η(ℓ²z)/η(z)`, with
`v_i ≥ d(i,j) = ⌈(ℓi − j − (ℓ+1)/2)/(ℓ+1)⌉ − 1`.

These are exactly the bounds of `docs/ATKIN_OBRIEN_PROOF.md` ("(UB)" under (I1), "(DB)" in Step 1),
column by column: column `j` of the matrix of `U` (resp. `D`) in Katz coordinates, i.e. the Katz
expansion of the image of `b/E^j`, has `v_i ≥ u(i,j)` (resp. `d(i,j)`). For `u(i,j) ≤ 0` the bound is
just integrality.

**`transfer`**: a column bound `mat` with `γ'(i) − 1 ≤ max(0, γ(j) − c) + mat(i,j)` for all `i, j`
maps `Env c γ` into `Env 1 γ'`. This is `AtkinOBrien.bridge` (finite sums of `ϖ^e`-multiples),
applied to the truncation mod `ℓ^N` of the infinite Katz series. With `AtkinOBrien.U_step` /
`AtkinOBrien.D_step` it gives `U(A_c(β)) ⊆ A₁(α)` and `D(A_c(α)) ⊆ A₁(β)` for `c ≤ 2` (`U_env`, `D_env`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AtkinOBrienFinal
open PowerSeries AtkinOBrien

variable (ℓ : ℕ) [hℓp : Fact ℓ.Prime] (hℓ : 5 ≤ ℓ)

/-- `Φ = q^δ (q^{ℓ²};q^{ℓ²})_∞/(q;q)_∞ ∈ ℤ_ℓ⟦q⟧`. -/
noncomputable def Φl : PS ℓ := PowerSeries.map (Int.castRingHom ℤ_[ℓ]) (BoylanWebb.Φ ℓ)

/-- `U_ℓ` as a `ℤ_ℓ`-linear map. -/
noncomputable def Ulin : PS ℓ →ₗ[ℤ_[ℓ]] PS ℓ where
  toFun := BoylanWebb.U ℓ
  map_add' f g := BoylanWebb.U_add ℓ f g
  map_smul' r f := by ext n; simp [BoylanWebb.coeff_U]

/-- `D = U_ℓ ∘ (Φ·)`. -/
noncomputable def Dlin : PS ℓ →ₗ[ℤ_[ℓ]] PS ℓ := Ulin ℓ ∘ₗ LinearMap.mulLeft ℤ_[ℓ] (Φl ℓ)

lemma Ulin_apply (f : PS ℓ) : Ulin ℓ f = BoylanWebb.U ℓ f := rfl
lemma Dlin_apply (f : PS ℓ) : Dlin ℓ f = BoylanWebb.U ℓ (Φl ℓ * f) := rfl

/-- **(UB)**: the `U`-matrix in Katz coordinates satisfies `v(U_{ij}) ≥ u(i,j)`. -/
def UB : Prop :=
  ∀ j, ∀ x ∈ Kpiece ℓ hℓ j, ∃ c : ℕ → Poly ℓ,
    IsKatz ℓ hℓ c (BoylanWebb.U ℓ (ModP.ev ℤ_[ℓ] x * Einv ℓ hℓ ^ j)) ∧
    ∀ i, AtkinOBrien.Dvd (ℓ : ℤ_[ℓ]) (u ℓ i j).toNat (c i)

/-- **(DB)**: the `D`-matrix in Katz coordinates satisfies `v(D_{ij}) ≥ d(i,j)`. -/
def DB : Prop :=
  ∀ j, ∀ x ∈ Kpiece ℓ hℓ j, ∃ c : ℕ → Poly ℓ,
    IsKatz ℓ hℓ c (BoylanWebb.U ℓ (Φl ℓ * (ModP.ev ℤ_[ℓ] x * Einv ℓ hℓ ^ j))) ∧
    ∀ i, AtkinOBrien.Dvd (ℓ : ℤ_[ℓ]) (d ℓ i j).toNat (c i)

/-- column bounds for a linear operator. -/
def Cols (Top : PS ℓ →ₗ[ℤ_[ℓ]] PS ℓ) (mat : ℕ → ℕ → ℤ) : Prop :=
  ∀ j, ∀ x ∈ Kpiece ℓ hℓ j, ∃ c : ℕ → Poly ℓ, IsKatz ℓ hℓ c (Top (ModP.ev ℤ_[ℓ] x * Einv ℓ hℓ ^ j)) ∧
    ∀ i, AtkinOBrien.Dvd (ℓ : ℤ_[ℓ]) (mat i j).toNat (c i)

lemma cols_U (h : UB ℓ hℓ) : Cols ℓ hℓ (Ulin ℓ) (u ℓ) := h
lemma cols_D (h : DB ℓ hℓ) : Cols ℓ hℓ (Dlin ℓ) (d ℓ) := h

variable {ℓ}

/-- **Envelope transfer** from column bounds. -/
theorem transfer (Top : PS ℓ →ₗ[ℤ_[ℓ]] PS ℓ) (mat : ℕ → ℕ → ℤ) (hcol : Cols ℓ hℓ Top mat) (c : ℤ)
    (γ γ' : ℕ → ℤ) (henv : ∀ i j, γ' i - 1 ≤ max 0 (γ j - c) + mat i j) (f : PS ℓ)
    (hf : Env ℓ hℓ c γ f) : Env ℓ hℓ 1 γ' (Top f) := by
  intro N
  obtain ⟨I, a, haK, ⟨g, hg⟩, hab⟩ := hf N
  set m : ℕ → ℕ := fun j => (max 0 (γ j - c)).toNat with hm
  choose y hy using hab
  have hyK : ∀ j, y j ∈ Kpiece ℓ hℓ j := fun j =>
    Kpiece_of_smul hℓ (pow_ne_zero _ ell_ne_zero) (by rw [← hy j]; exact haK j)
  choose cc hcK hcb using fun j => hcol j (y j) (hyK j)
  choose Ij hIj using fun j => (hcK j).2 N
  set Is := (Finset.range I).sup Ij with hIs
  have hh0 : ∀ j ∈ Finset.range I, ∃ h : PS ℓ, Top (ModP.ev ℤ_[ℓ] (y j) * Einv ℓ hℓ ^ j) -
      ∑ i ∈ Finset.range Is, ModP.ev ℤ_[ℓ] (cc j i) * Einv ℓ hℓ ^ i = (ℓ : ℤ_[ℓ]) ^ N • h :=
    fun j hj => hIj j Is (Finset.le_sup (f := Ij) hj)
  choose! h hh using hh0
  refine ⟨Is, fun i => ∑ j ∈ Finset.range I, (ℓ : ℤ_[ℓ]) ^ m j • cc j i, fun i =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ((hcK j).1 i), ⟨Top g + ∑ j ∈ Finset.range I,
      (ℓ : ℤ_[ℓ]) ^ m j • h j, ?_⟩, fun i => ?_⟩
  · have hf' : f = ∑ j ∈ Finset.range I, ModP.ev ℤ_[ℓ] (a j) * Einv ℓ hℓ ^ j + (ℓ : ℤ_[ℓ]) ^ N • g := by
      rw [← hg]; abel
    have e1 : Top f = ∑ j ∈ Finset.range I, (ℓ : ℤ_[ℓ]) ^ m j • Top (ModP.ev ℤ_[ℓ] (y j) * Einv ℓ hℓ ^ j) +
        (ℓ : ℤ_[ℓ]) ^ N • Top g := by
      rw [hf', map_add, map_sum, map_smul]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hy j, map_smul, smul_mul_assoc, map_smul]
    have e3 : ∑ i ∈ Finset.range Is, ModP.ev ℤ_[ℓ] (∑ j ∈ Finset.range I, (ℓ : ℤ_[ℓ]) ^ m j • cc j i) *
          Einv ℓ hℓ ^ i =
        ∑ j ∈ Finset.range I, (ℓ : ℤ_[ℓ]) ^ m j •
          ∑ i ∈ Finset.range Is, ModP.ev ℤ_[ℓ] (cc j i) * Einv ℓ hℓ ^ i := by
      simp only [map_sum, map_smul, Finset.sum_mul, smul_mul_assoc, Finset.smul_sum]
      exact Finset.sum_comm
    have e2 : ∑ j ∈ Finset.range I, (ℓ : ℤ_[ℓ]) ^ m j • Top (ModP.ev ℤ_[ℓ] (y j) * Einv ℓ hℓ ^ j) =
        ∑ j ∈ Finset.range I, (ℓ : ℤ_[ℓ]) ^ m j •
          (∑ i ∈ Finset.range Is, ModP.ev ℤ_[ℓ] (cc j i) * Einv ℓ hℓ ^ i + (ℓ : ℤ_[ℓ]) ^ N • h j) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [← hh j hj]; abel_nf
    rw [e1, e3, e2, smul_add, Finset.smul_sum]
    simp only [smul_add, Finset.sum_add_distrib]
    rw [show ∑ j ∈ Finset.range I, (ℓ : ℤ_[ℓ]) ^ m j • (ℓ : ℤ_[ℓ]) ^ N • h j =
        ∑ j ∈ Finset.range I, (ℓ : ℤ_[ℓ]) ^ N • (ℓ : ℤ_[ℓ]) ^ m j • h j from
      Finset.sum_congr rfl fun j _ => smul_comm _ _ _]
    abel
  · refine AtkinOBrien.Dvd.sum _ _ fun j _ => ?_
    obtain ⟨z, hz⟩ := hcb j i
    refine Dvd_mono (b := m j + (mat i j).toNat) ?_ ⟨z, by rw [hz, smul_smul, ← pow_add]⟩
    have := henv i j
    simp only [hm]
    omega

/-- **`U(A_c(β)) ⊆ A₁(α)`** for `c ≤ 2`, from (UB). -/
theorem U_env (hℓ13 : 13 ≤ ℓ) (hUB : UB ℓ hℓ) (c : ℤ) (hc : c ≤ 2) (f : PS ℓ)
    (hf : Env ℓ hℓ c (β ℓ) f) : Env ℓ hℓ 1 (α ℓ) (Ulin ℓ f) :=
  transfer hℓ (Ulin ℓ) (u ℓ) (cols_U ℓ hℓ hUB) c (β ℓ) (α ℓ) (U_step hℓ13 c hc) f hf

/-- **`D(A_c(α)) ⊆ A₁(β)`** for `c ≤ 2`, from (DB). -/
theorem D_env (hℓ13 : 13 ≤ ℓ) (hDB : DB ℓ hℓ) (c : ℤ) (hc : c ≤ 2) (f : PS ℓ)
    (hf : Env ℓ hℓ c (α ℓ) f) : Env ℓ hℓ 1 (β ℓ) (Dlin ℓ f) :=
  transfer hℓ (Dlin ℓ) (d ℓ) (cols_D ℓ hℓ hDB) c (α ℓ) (β ℓ) (D_step hℓ13 c hc) f hf

end AtkinOBrienFinal
