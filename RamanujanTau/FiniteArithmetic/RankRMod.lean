import RamanujanTau.FiniteArithmetic.EnvelopeReduction
import RamanujanTau.AtkinOBrienFinal.Transfer
import RamanujanTau.AtkinOBrienFinal.Main

/-!
# Order-`r` data modulo `ℓ` with `s + r` forms

The `RankSMod` setup with `dim S_{ℓ-1} = s + r` (`r = 3`, `s = 2`: `ℓ = 61, 67, 71`).
Fix integral cusp forms `f₀, …, f_{s+r-1}` of weight `ℓ - 1` whose coefficients `a₁, …, a_{s+r}`
modulo `ℓ` form an invertible matrix `B`. Then every form of weight `ℓ - 1` is, modulo `ℓ`, a constant plus a combination
of the `fᵢ` (Sturm). The data `Umat`, `Dmat`, `seed` give `U` and `D = U(Δ^δ ·)` in these
coordinates. The odd and even partition series `L(b)` are then explicit coordinate vectors.
-/
set_option autoImplicit false

namespace RamanujanTau.FiniteArithmetic.RankR
open PowerSeries BoylanWebb AtkinOBrien AtkinOBrienFinal

variable {ℓ s r : ℕ} [hℓ : Fact ℓ.Prime]

/-- Matrix–vector product. -/
def mv {m n : ℕ} (M : Fin m → Fin n → ZMod ℓ) (v : Fin n → ZMod ℓ) : Fin m → ZMod ℓ :=
  fun j => ∑ i, M j i * v i

/-- The mod-`ℓ` data. -/
structure Data (ℓ s r : ℕ) [Fact ℓ.Prime] where
  f : Fin (s + r) → PowerSeries ℤ
  form : ∀ i, IntForm ((ℓ - 1 : ℕ) : ℤ) (f i)
  cusp : ∀ i, coeff 0 (f i) = 0
  hsturm : (ℓ - 1) / 12 + 1 ≤ s + r + 1
  hℓ5 : 5 ≤ ℓ
  /-- `B k i = a_{k+1}(fᵢ)`. -/
  B : Fin (s + r) → Fin (s + r) → ZMod ℓ
  hB : ∀ k i, coeff (k.val + 1) (Ψ ℓ (f i)) = B k i
  Binv : Fin (s + r) → Fin (s + r) → ZMod ℓ
  hBBinv : ∀ k j, ∑ i, B k i * Binv i j = if k = j then 1 else 0
  Umat : Fin (s + r) → Fin (s + r) → ZMod ℓ
  hU : ∀ i, U ℓ (Ψ ℓ (f i)) = ∑ j, C (Umat j i) * Ψ ℓ (f j)
  Dmat : Fin (s + r) → Fin (s + r) → ZMod ℓ
  hD : ∀ i, U ℓ (Ψ ℓ (Dz ^ δ ℓ) * Ψ ℓ (f i)) = ∑ j, C (Dmat j i) * Ψ ℓ (f j)
  seed : Fin (s + r) → ZMod ℓ
  hseed : U ℓ (Ψ ℓ (Dz ^ δ ℓ)) = ∑ j, C (seed j) * Ψ ℓ (f j)


lemma intForm_sum {k : ℤ} {ι : Type*} (t : Finset ι) (g : ι → PowerSeries ℤ)
    (h : ∀ i ∈ t, IntForm k (g i)) : IntForm k (∑ i ∈ t, g i) :=
  Finset.sum_induction _ (IntForm k) (fun _ _ => IntForm.add) IntForm.zero h

lemma reduce_D (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) (F : PS ℓ) :
    PowerSeries.map (PadicInt.toZMod (p := ℓ)) (Dlin ℓ F) =
      U ℓ (Ψ ℓ (Dz ^ δ ℓ) * PowerSeries.map (PadicInt.toZMod (p := ℓ)) F) := by
  rw [Dlin_apply, map_U, map_mul, Φl, map_map_int, Ψ_Φ ℓ h24]

lemma reduce_U (F : PS ℓ) :
    PowerSeries.map (PadicInt.toZMod (p := ℓ)) (Ulin ℓ F) =
      U ℓ (PowerSeries.map (PadicInt.toZMod (p := ℓ)) F) := by
  rw [Ulin_apply, map_U]

namespace Data
variable (D : Data ℓ s r)

/-- The form with coordinates `e`. -/
noncomputable def comb (e : Fin (s + r) → ZMod ℓ) : PowerSeries (ZMod ℓ) := ∑ j, C (e j) * Ψ ℓ (D.f j)

lemma coeff_comb (e : Fin (s + r) → ZMod ℓ) (k : Fin (s + r)) :
    coeff (k.val + 1) (D.comb e) = ∑ i, D.B k i * e i := by
  simp only [comb, map_sum, coeff_C_mul, D.hB]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma coeff_zero_comb (e : Fin (s + r) → ZMod ℓ) : coeff 0 (D.comb e) = 0 := by
  simp only [comb, map_sum, coeff_C_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [show coeff 0 (Ψ ℓ (D.f i)) = 0 by rw [coeff_map, D.cusp i, map_zero], mul_zero]

lemma comb_add (e e' : Fin (s + r) → ZMod ℓ) : D.comb (e + e') = D.comb e + D.comb e' := by
  simp only [comb, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

lemma comb_smul (c : ZMod ℓ) (e : Fin (s + r) → ZMod ℓ) : D.comb (c • e) = C c * D.comb e := by
  simp only [comb, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

lemma U_sum (e : Fin (s + r) → PowerSeries (ZMod ℓ)) : U ℓ (∑ j, e j) = ∑ j, U ℓ (e j) := by
  classical
  have : ∀ t : Finset (Fin (s + r)), U ℓ (∑ j ∈ t, e j) = ∑ j ∈ t, U ℓ (e j) := fun t => by
    induction t using Finset.induction_on with
    | empty => ext n; simp [coeff_U]
    | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, U_add, ih]
  exact this _

lemma U_comb (e : Fin (s + r) → ZMod ℓ) : U ℓ (D.comb e) = D.comb (mv D.Umat e) := by
  simp only [comb, U_sum, U_C_mul, D.hU, mv, Finset.mul_sum, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_assoc, ← map_mul, mul_comm (e i)]

lemma D_comb (e : Fin (s + r) → ZMod ℓ) :
    U ℓ (Ψ ℓ (Dz ^ δ ℓ) * D.comb e) = D.comb (mv D.Dmat e) := by
  simp only [comb, Finset.mul_sum, mul_left_comm (Ψ ℓ (Dz ^ δ ℓ)), U_sum, U_C_mul, D.hD, mv,
    map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_assoc, ← map_mul, mul_comm (e i)]

/-- **Sturm span**: a form of weight `ℓ - 1` is a constant plus a combination of the `fᵢ`. -/
theorem span (a : PowerSeries ℤ) (ha : IntForm ((ℓ - 1 : ℕ) : ℤ) a) :
    Ψ ℓ a = C (coeff 0 (Ψ ℓ a)) +
      D.comb (fun i => ∑ k : Fin (s + r), D.Binv i k * coeff (k.val + 1) (Ψ ℓ a)) := by
  obtain ⟨A, hA, hAbar⟩ := exists_hasse_lift ℓ D.hℓ5
  set c₀ := coeff 0 (Ψ ℓ a)
  set e : Fin (s + r) → ZMod ℓ := fun i => ∑ k : Fin (s + r), D.Binv i k * coeff (k.val + 1) (Ψ ℓ a)
  let lift : ZMod ℓ → ℤ := fun c => c.val
  have hC (c : ZMod ℓ) : Ψ ℓ (C (lift c)) = C c := by
    rw [PowerSeries.map_C, eq_intCast, Int.cast_natCast, ZMod.natCast_zmod_val]
  let rem := a - C (lift c₀) * A - ∑ j, C (lift (e j)) * D.f j
  have hr : IntForm ((ℓ - 1 : ℕ) : ℤ) rem := by
    exact (ha.sub (hA.C_mul _)).sub (intForm_sum _ _ fun j _ => (D.form j).C_mul _)
  have hbar : Ψ ℓ rem = Ψ ℓ a - C c₀ - D.comb e := by
    simp only [rem, map_sub, map_mul, hC, hAbar, mul_one, map_sum, comb]
  have hz : Ψ ℓ rem = 0 := by
    apply BoylanWebb.sturm ℓ (s + r + 1) _ (by have := D.hsturm; push_cast; omega) rem hr
    refine (pow_dvd_pow (X : PowerSeries (ZMod ℓ))
      (show (((ℓ - 1 : ℕ) : ℤ)).toNat / 12 + 1 ≤ s + r + 1 by
        have := D.hsturm; rw [Int.toNat_natCast]; omega)).trans ?_
    rw [PowerSeries.X_pow_dvd_iff]
    intro n hn
    rw [hbar, map_sub, map_sub, coeff_C]
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [if_pos rfl, D.coeff_zero_comb]; simp [c₀]
    · obtain ⟨k, rfl⟩ : ∃ k : Fin (s + r), n = k.val + 1 := ⟨⟨n - 1, by omega⟩, by simp only; omega⟩
      rw [if_neg (by omega), D.coeff_comb]
      simp only [e, Finset.mul_sum, sub_zero]
      rw [Finset.sum_comm]
      have : ∀ j : Fin (s + r), ∑ i, D.B k i * (D.Binv i j * coeff (j.val + 1) (Ψ ℓ a)) =
          (if k = j then 1 else 0) * coeff (j.val + 1) (Ψ ℓ a) := fun j => by
        rw [← D.hBBinv k j, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
      simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      ring
  rw [hbar] at hz
  linear_combination hz

/-- A form of weight `ℓ - 1` with `a₀ = 0` is the combination read off from `a₁, …, a_{s+r}`. -/
theorem cusp_eq (a : PowerSeries ℤ) (ha : IntForm ((ℓ - 1 : ℕ) : ℤ) a) (h0 : coeff 0 (Ψ ℓ a) = 0) :
    Ψ ℓ a = D.comb (fun i => ∑ k : Fin (s + r), D.Binv i k * coeff (k.val + 1) (Ψ ℓ a)) := by
  conv_lhs => rw [D.span a ha]
  rw [h0, map_zero, zero_add]

/-- Coordinates are determined by `a₁, …, a_{s+r}`. -/
theorem comb_eq_of_coeff {e e' : Fin (s + r) → ZMod ℓ}
    (h : ∀ k : Fin (s + r), coeff (k.val + 1) (D.comb e) = coeff (k.val + 1) (D.comb e')) :
    D.comb e = D.comb e' := by
  -- lift both to integral forms
  let lift : ZMod ℓ → ℤ := fun c => c.val
  have hC (c : ZMod ℓ) : Ψ ℓ (C (lift c)) = C c := by
    rw [PowerSeries.map_C, eq_intCast, Int.cast_natCast, ZMod.natCast_zmod_val]
  let a := ∑ j, C (lift (e j)) * D.f j - ∑ j, C (lift (e' j)) * D.f j
  have ha : IntForm ((ℓ - 1 : ℕ) : ℤ) a := by
    exact (intForm_sum _ _ fun j _ => (D.form j).C_mul _).sub
      (intForm_sum _ _ fun j _ => (D.form j).C_mul _)
  have hΨ : Ψ ℓ a = D.comb e - D.comb e' := by
    simp only [a, map_sub, map_sum, map_mul, hC, comb]
  have hz : Ψ ℓ a = 0 := by
    apply BoylanWebb.sturm ℓ (s + r + 1) _ (by have := D.hsturm; push_cast; omega) a ha
    refine (pow_dvd_pow (X : PowerSeries (ZMod ℓ))
      (show (((ℓ - 1 : ℕ) : ℤ)).toNat / 12 + 1 ≤ s + r + 1 by
        have := D.hsturm; rw [Int.toNat_natCast]; omega)).trans ?_
    rw [PowerSeries.X_pow_dvd_iff]
    intro n hn
    rw [hΨ, map_sub]
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [D.coeff_zero_comb, D.coeff_zero_comb, sub_zero]
    · obtain ⟨k, rfl⟩ : ∃ k : Fin (s + r), n = k.val + 1 := ⟨⟨n - 1, by omega⟩, by simp only; omega⟩
      rw [h k, sub_self]
  rw [hΨ] at hz
  exact sub_eq_zero.mp hz

/-! ### The partition series modulo `ℓ` -/

/-- Odd coordinates: `o₀ = seed`, `o_{n+1} = Dmat (Umat o_n)`. -/
def odd : ℕ → Fin (s + r) → ZMod ℓ
  | 0 => D.seed
  | n + 1 => mv D.Dmat (mv D.Umat (odd n))

variable (h24 : 24 * δ ℓ + 1 = ℓ ^ 2)
include h24

lemma odd_reduction (n : ℕ) :
    PowerSeries.map (PadicInt.toZMod (p := ℓ)) (Ll ℓ (2 * n + 1)) = D.comb (D.odd n) := by
  induction n with
  | zero =>
    have h1 : Ll ℓ 1 = Dlin ℓ (Ll ℓ 0) := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, Ll_succ, Tl, if_pos ⟨0, rfl⟩]
    rw [show 2 * 0 + 1 = 1 from rfl, h1, reduce_D h24,
      show Ll ℓ 0 = 1 by simp [Ll, L], map_one, mul_one, D.hseed]
    rfl
  | succ n ih =>
    have h1 : Ll ℓ (2 * (n + 1) + 1) = Dlin ℓ (Ulin ℓ (Ll ℓ (2 * n + 1))) := by
      rw [Ll_succ, Tl, if_pos (by rw [show 2 * (n + 1) = 2 * (n + 1) by rfl]; exact even_two_mul _),
        show 2 * (n + 1) = (2 * n + 1) + 1 by ring, Ll_succ, Tl,
        if_neg (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one n))]
    rw [h1, reduce_D h24, reduce_U, ih, D.U_comb, D.D_comb]
    rfl

lemma even_reduction (n : ℕ) :
    PowerSeries.map (PadicInt.toZMod (p := ℓ)) (Ll ℓ (2 * n + 2)) = D.comb (mv D.Umat (D.odd n)) := by
  have h1 : Ll ℓ (2 * n + 2) = Ulin ℓ (Ll ℓ (2 * n + 1)) := by
    rw [show 2 * n + 2 = (2 * n + 1) + 1 by ring, Ll_succ, Tl,
      if_neg (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one n))]
  rw [h1, reduce_U, D.odd_reduction h24, D.U_comb]

end Data

end RamanujanTau.FiniteArithmetic.RankR
