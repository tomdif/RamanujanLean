import RamanujanTau.FiniteArithmetic.InverseCertificate

/-! Assemble finite product certificates from bounded blocks. Each numerical
check has a small left factor; the assembly preserves the full series congruence. -/
set_option autoImplicit false
namespace BoylanWebb
open PowerSeries RamanujanTau

theorem forall_Ico_join {P : ℕ → Prop} {a b c : ℕ}
    (h₁ : ∀ n ∈ Finset.Ico a b, P n) (h₂ : ∀ n ∈ Finset.Ico b c, P n) :
    ∀ n ∈ Finset.Ico a c, P n := by
  intro n hn
  obtain ⟨ha, hc⟩ := Finset.mem_Ico.mp hn
  by_cases hb : n < b
  · exact h₁ n (Finset.mem_Ico.mpr ⟨ha, hb⟩)
  · exact h₂ n (Finset.mem_Ico.mpr ⟨Nat.le_of_not_gt hb, hc⟩)

theorem toPS_append (a b : List ℤ) :
    toPS (a ++ b) = toPS a + X ^ a.length * toPS b := by
  induction a with
  | nil => simp [toPS_nil]
  | cons x xs ih =>
    rw [List.cons_append, toPS_cons, ih, toPS_cons, List.length_cons, pow_succ]
    ring

theorem Cg.shift_precision {ℓ d : ℕ} {F G : PowerSeries ℤ}
    (h : Cg ℓ d F G) (k : ℕ) :
    Cg ℓ (d + k) (X ^ k * F) (X ^ k * G) := by
  rcases h with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  simp only [map_mul, map_pow, map_X, ← mul_sub]
  rw [hc, show d + k + 1 = k + (d + 1) by omega, pow_add]
  ring

/-- One block of a product, with the remaining tail already certified at the
lower precision needed after shifting by the block length. -/
theorem Cg_mul_block {ℓ d k : ℕ} {a tail b carry out : List ℤ}
    (hlen : a.length = k)
    (ht : Cg ℓ d (toPS tail * toPS b) (toPS carry))
    (hc : red ℓ (truncList (d + k)
      (addList (mulList a b) (shiftList k carry))) = out) :
    Cg ℓ (d + k) (toPS (a ++ tail) * toPS b) (toPS out) := by
  rw [toPS_append, hlen, add_mul, mul_assoc]
  refine ((Cg.refl (toPS a * toPS b)).add (ht.shift_precision k)).trans ?_
  rw [← toPS_mulList, ← toPS_shiftList, ← toPS_addList, ← hc]
  exact ((Cg_red _).trans (Cg_trunc _)).symm

/-- Use a checked list-product congruence to certify a true product. -/
theorem Cg_product {ℓ d : ℕ} {F G : PowerSeries ℤ} {a b out : List ℤ}
    (hF : Cg ℓ d F (toPS a)) (hG : Cg ℓ d G (toPS b))
    (hcheck : Cg ℓ d (toPS a * toPS b) (toPS out)) :
    Cg ℓ d (F * G) (toPS out) := (hF.mul hG).trans hcheck

/-- Inverse certificates need only a product congruence, independently of the
algorithm used to check that product. -/
theorem Cg_inverse_product {ℓ d : ℕ} {F G : PowerSeries ℤ} (hFG : F * G = 1)
    {a b : List ℤ} (hF : Cg ℓ d F (toPS a))
    (hcheck : Cg ℓ d (toPS a * toPS b) 1) : Cg ℓ d G (toPS b) := by
  have h := (hF.mul (Cg.refl (toPS b))).trans hcheck
  have hmul : Ψ ℓ F * Ψ ℓ G = 1 := by rw [← map_mul, hFG, map_one]
  have he : Ψ ℓ G - Ψ ℓ (toPS b) = -(Ψ ℓ G * (Ψ ℓ (F * toPS b) - Ψ ℓ 1)) := by
    rw [map_mul, map_one]
    linear_combination (Ψ ℓ (toPS b)) * hmul
  unfold Cg at h ⊢
  rw [he]
  exact dvd_neg.mpr (Dvd.dvd.mul_left h _)

end BoylanWebb
