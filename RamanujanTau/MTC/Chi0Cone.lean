/-
# Positive cones of `f_{12,9,3}` and their shift relations (the χ₀ lattice bookkeeping)

With `Q = t⁶` (so `Q`-exponent `E` is `t^{6E}`), the positive cone of `f_{12,9,3}(−Q^{ex}, Q^{ey}, Q)` is

  `Cp k ex ey = Σ_{r,s≥0} (−1)^s Q^{k + ex·r + ey·s + 12C(r,2) + 9rs + 3C(s,2)}`.

Splitting off the row `r = 0` (resp. the column `s = 0`) gives the two shift relations
* `Cp_shift_r`: `Cp k ex ey = Th3 k ey + Cp (k+ex) (ex+12) (ey+9)`;
* `Cp_shift_s`: `Cp k ex ey = Th12 k ex − Cp (k+ey) (ex+9) (ey+3)`,

with the partial thetas `Th3 k e = Σ_{s≥0} (−1)^s Q^{k+es+3C(s,2)}` and `Th12 k e = Σ_{r≥0} Q^{k+er+12C(r,2)}`.
-/
import RamanujanTau.MTC.Hecke373

set_option autoImplicit false

namespace MTC.Chi0L
open ALz HahnSeries Finset MTC

/-! ## Splitting a summable family along `κ₁ ⊕ κ₂ ≃ ι` -/

section Split
variable {ι κ₁ κ₂ : Type*}

theorem hs_split (s : SummableFamily ℤ ℂ ι) (a : SummableFamily ℤ ℂ κ₁) (b : SummableFamily ℤ ℂ κ₂)
    (e : κ₁ ⊕ κ₂ ≃ ι) (ha : ∀ i, s (e (Sum.inl i)) = a i) (hb : ∀ j, s (e (Sum.inr j)) = b j) :
    hs s = hs a + hs b := by
  let A : SummableFamily ℤ ℂ (κ₁ ⊕ κ₂) := a.embDomain ⟨Sum.inl, Sum.inl_injective⟩
  let B : SummableFamily ℤ ℂ (κ₁ ⊕ κ₂) := b.embDomain ⟨Sum.inr, Sum.inr_injective⟩
  have hA : hs A = hs a := by rw [hs_eq, hs_eq, SummableFamily.hsum_embDomain]
  have hB : hs B = hs b := by rw [hs_eq, hs_eq, SummableFamily.hsum_embDomain]
  have h : hs s = 1 * hs (A + B) := hsum_reindex _ _ e 1 fun x => by
    rw [one_mul, SummableFamily.add_apply]
    rcases x with i | j
    · have h1 : A (Sum.inl i) = a i := SummableFamily.embDomain_image _ _
      have h2 : B (Sum.inl i) = 0 := by apply SummableFamily.embDomain_notin_range; simp
      rw [ha, h1, h2, add_zero]
    · have h1 : B (Sum.inr j) = b j := SummableFamily.embDomain_image _ _
      have h2 : A (Sum.inr j) = 0 := by apply SummableFamily.embDomain_notin_range; simp
      rw [hb, h1, h2, zero_add]
  rw [h, one_mul, hs_eq, SummableFamily.hsum_add, ← hs_eq, ← hs_eq, hA, hB]

lemma hs_unique {ι : Type*} [Unique ι] (s : SummableFamily ℤ ℂ ι) : hs s = s default := by
  rw [hs_eq_finset_sum Finset.univ (fun i hi => absurd (Finset.mem_univ i) hi)]
  simp

end Split

/-- `ℕ ≃ Unit ⊕ ℕ`, `0 ↦ ()`, `n+1 ↦ n`. -/
def eNat : Unit ⊕ ℕ ≃ ℕ where
  toFun x := Sum.elim (fun _ => 0) (· + 1) x
  invFun n := if n = 0 then Sum.inl () else Sum.inr (n - 1)
  left_inv x := by rcases x with _ | n <;> simp
  right_inv n := by rcases n with _ | n <;> simp

/-- `ℕ × ℕ ≃ ℕ ⊕ ℕ × ℕ`: the row `r = 0`, and `(r+1, s)`. -/
def eRow : ℕ ⊕ ℕ × ℕ ≃ ℕ × ℕ where
  toFun x := Sum.elim (fun s => (0, s)) (fun p => (p.1 + 1, p.2)) x
  invFun p := if p.1 = 0 then Sum.inl p.2 else Sum.inr (p.1 - 1, p.2)
  left_inv x := by rcases x with s | ⟨r, s⟩ <;> simp
  right_inv p := by
    obtain ⟨r, s⟩ := p
    rcases r with _ | r <;> simp

/-- `ℕ × ℕ ≃ ℕ ⊕ ℕ × ℕ`: the column `s = 0`, and `(r, s+1)`. -/
def eCol : ℕ ⊕ ℕ × ℕ ≃ ℕ × ℕ where
  toFun x := Sum.elim (fun r => (r, 0)) (fun p => (p.1, p.2 + 1)) x
  invFun p := if p.2 = 0 then Sum.inl p.1 else Sum.inr (p.1, p.2 - 1)
  left_inv x := by rcases x with s | ⟨r, s⟩ <;> simp
  right_inv p := by
    obtain ⟨r, s⟩ := p
    rcases s with _ | s <;> simp

/-! ## Cones and partial thetas -/

lemma c2_nat_nonneg (n : ℕ) : 0 ≤ c2 n := c2_nonneg _

lemma c2_nat_ge (n : ℕ) : (n : ℤ) - 1 ≤ c2 n := by
  have := two_c2 (n : ℤ)
  rcases n with _ | _ | n
  · simp [c2]
  · simp [c2]
  · push_cast at this ⊢; nlinarith

/-- the `Q`-exponent of the cone. -/
def cE (k ex ey : ℕ) (p : ℕ × ℕ) : ℤ :=
  6 * ((k : ℤ) + ex * p.1 + ey * p.2 + 12 * c2 p.1 + 9 * p.1 * p.2 + 3 * c2 p.2)

lemma cE_ge (k ex ey : ℕ) (p : ℕ × ℕ) : (p.1 : ℤ) + p.2 - 2 ≤ cE k ex ey p := by
  unfold cE
  have := c2_nat_ge p.1; have := c2_nat_ge p.2; have := c2_nat_nonneg p.1; have := c2_nat_nonneg p.2
  have : (0 : ℤ) ≤ (ex : ℤ) * p.1 := by positivity
  have : (0 : ℤ) ≤ (ey : ℤ) * p.2 := by positivity
  have : (0 : ℤ) ≤ 9 * (p.1 : ℤ) * p.2 := by positivity
  have : (0 : ℤ) ≤ k := by positivity
  omega

lemma box2_fin (n : ℤ) (E : ℕ × ℕ → ℤ) (h : ∀ p, (p.1 : ℤ) + p.2 - 2 ≤ E p) : {p | E p = n}.Finite :=
  ((Finset.range (n.toNat + 3) ×ˢ Finset.range (n.toNat + 3) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)).toFinite.subset
    fun p hp => by
      have := h p
      simp only [Set.mem_setOf_eq] at hp
      simp only [Finset.coe_product, Set.mem_prod, Finset.coe_range, Set.mem_Iio]
      omega

noncomputable def cpF (k ex ey : ℕ) : SummableFamily ℤ ℂ (ℕ × ℕ) :=
  monoFam (cE k ex ey) (fun p => (-1) ^ p.2) (-2) (fun p => by have := cE_ge k ex ey p; omega)
    (fun n => box2_fin n _ (cE_ge k ex ey))

/-- the positive cone `Σ_{r,s≥0} (−1)^s Q^{k+ex r+ey s+12C(r,2)+9rs+3C(s,2)}`. -/
noncomputable def Cp (k ex ey : ℕ) : L := hs (cpF k ex ey)

def tE3 (k e : ℕ) (s : ℕ) : ℤ := 6 * ((k : ℤ) + e * s + 3 * c2 s)
def tE12 (k e : ℕ) (r : ℕ) : ℤ := 6 * ((k : ℤ) + e * r + 12 * c2 r)

lemma tE3_ge (k e s : ℕ) : (s : ℤ) - 1 ≤ tE3 k e s := by
  unfold tE3; have := c2_nat_ge s; have := c2_nat_nonneg s; have : (0 : ℤ) ≤ (e : ℤ) * s := by positivity
  have : (0 : ℤ) ≤ k := by positivity
  omega
lemma tE12_ge (k e r : ℕ) : (r : ℤ) - 1 ≤ tE12 k e r := by
  unfold tE12; have := c2_nat_ge r; have := c2_nat_nonneg r; have : (0 : ℤ) ≤ (e : ℤ) * r := by positivity
  have : (0 : ℤ) ≤ k := by positivity
  omega

lemma line_fin (n : ℤ) (E : ℕ → ℤ) (h : ∀ s : ℕ, (s : ℤ) - 1 ≤ E s) : {s | E s = n}.Finite :=
  (Set.finite_Iic (n.toNat + 1)).subset fun s hs => by
    have := h s; simp only [Set.mem_setOf_eq] at hs; simp only [Set.mem_Iic]; omega

noncomputable def th3F (k e : ℕ) : SummableFamily ℤ ℂ ℕ :=
  monoFam (tE3 k e) (fun s => (-1) ^ s) (-1) (fun s => by have := tE3_ge k e s; omega)
    (fun n => line_fin n _ (tE3_ge k e))
noncomputable def th12F (k e : ℕ) : SummableFamily ℤ ℂ ℕ :=
  monoFam (tE12 k e) (fun _ => 1) (-1) (fun r => by have := tE12_ge k e r; omega)
    (fun n => line_fin n _ (tE12_ge k e))

/-- `Σ_{s≥0} (−1)^s Q^{k+es+3C(s,2)}`. -/
noncomputable def Th3 (k e : ℕ) : L := hs (th3F k e)
/-- `Σ_{r≥0} Q^{k+er+12C(r,2)}`. -/
noncomputable def Th12 (k e : ℕ) : L := hs (th12F k e)

/-! ## The shift relations -/

lemma neg_mono (E : ℤ) (C : ℂ) : -(mono E C : L) = mono E (-C) := by simp [mono]

theorem Cp_shift_r (k ex ey : ℕ) : Cp k ex ey = Th3 k ey + Cp (k + ex) (ex + 12) (ey + 9) :=
  hs_split _ _ _ eRow
    (fun s => by
      simp only [cpF, th3F, monoFam_apply, eRow, Equiv.coe_fn_mk, Sum.elim_inl]
      exact mono_ext (by unfold cE tE3; simp [c2]) rfl)
    (fun p => by
      simp only [cpF, monoFam_apply, eRow, Equiv.coe_fn_mk, Sum.elim_inr]
      refine mono_ext ?_ rfl
      unfold cE
      push_cast
      rw [show ((p.1 : ℤ) + 1) = p.1 + 1 from rfl, c2_succ]
      ring)

theorem Cp_shift_s (k ex ey : ℕ) : Cp k ex ey = Th12 k ex - Cp (k + ey) (ex + 9) (ey + 3) := by
  rw [sub_eq_add_neg, Cp, Cp]
  have : hs (cpF k ex ey) = hs (th12F k ex) + hs ((-1 : L) • cpF (k + ey) (ex + 9) (ey + 3)) :=
    hs_split _ _ _ eCol
      (fun r => by
        simp only [cpF, th12F, monoFam_apply, eCol, Equiv.coe_fn_mk, Sum.elim_inl]
        exact mono_ext (by unfold cE tE12; simp [c2]) (by simp))
      (fun p => by
        simp only [cpF, monoFam_apply, eCol, Equiv.coe_fn_mk, Sum.elim_inr, SummableFamily.smul_apply,
          HahnSeries.of_symm_smul_of_eq_mul]
        rw [neg_one_mul, neg_mono]
        refine mono_ext ?_ (by rw [pow_succ]; ring)
        unfold cE
        push_cast
        rw [c2_succ]
        ring)
  rw [this, Th12, hs_eq, hs_eq, hs_eq, SummableFamily.hsum_smul]
  ring

end MTC.Chi0L
