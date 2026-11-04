/-
# Kloosterman sums over `ZMod c`: bridge, unit scaling, twisted multiplicativity

`kl c a b = ∑_{u ∈ (ZMod c)ˣ} ψ_c(a u + b u⁻¹)`, `ψ_c = ZMod.stdAddChar` (`ψ_c(j) = e(j/c)`).

* `kloosterman_eq_kl`: the `Finset.range` definition `kloosterman m n c` equals `kl c m n`;
* `kl_mul_left_unit`: `S(t a, b) = S(a, t b)` for a unit `t`;
* `kl_mul_coprime`: twisted multiplicativity `S(m,n;qr) = S(u m, u n; q) S(v m, v n; r)`
  when `u r + v q = 1`.
-/
import RamanujanTau.TauBound.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

set_option autoImplicit false

namespace RamanujanTau.TauBound

open Complex
open scoped Real

/-- The Kloosterman sum on `ZMod c`. -/
noncomputable def kl (c : ℕ) [NeZero c] (a b : ZMod c) : ℂ :=
  ∑ u : (ZMod c)ˣ, ZMod.stdAddChar (a * (u : ZMod c) + b * ((u⁻¹ : (ZMod c)ˣ) : ZMod c))

lemma stdAddChar_intCast_eq_ee (c : ℕ) [NeZero c] (k : ℤ) :
    ZMod.stdAddChar (k : ZMod c) = ee ((k : ℂ) / c) := by
  rw [ZMod.stdAddChar_coe, ee]; ring_nf

lemma stdAddChar_eq_ee_val (c : ℕ) [NeZero c] (x : ZMod c) :
    ZMod.stdAddChar x = ee ((x.val : ℂ) / c) := by
  have := stdAddChar_intCast_eq_ee c (x.val : ℤ)
  simpa [ZMod.natCast_zmod_val] using this

lemma norm_stdAddChar (c : ℕ) [NeZero c] (x : ZMod c) : ‖ZMod.stdAddChar x‖ = 1 := by
  rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _

/-- Bridge from the `Finset.range` definition. -/
theorem kloosterman_eq_kl (m n : ℤ) (c : ℕ) [NeZero c] :
    kloosterman m n c = kl c m n := by
  unfold kloosterman kl
  refine Finset.sum_bij' (fun d hd => ZMod.unitOfCoprime d (Finset.mem_filter.mp hd).2)
    (fun u _ => (u : ZMod c).val) (fun _ _ => Finset.mem_univ _) (fun u _ => ?_) (fun d hd => ?_)
    (fun u _ => ?_) (fun d hd => ?_)
  · simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨ZMod.val_lt _, ZMod.val_coe_unit_coprime u⟩
  · have hd' := Finset.mem_filter.mp hd
    simp only [ZMod.coe_unitOfCoprime]
    exact ZMod.val_cast_of_lt (Finset.mem_range.mp hd'.1)
  · ext; simp [ZMod.coe_unitOfCoprime]
  · have key : ((m * d + n * (((d : ZMod c)⁻¹).val : ℤ) : ℤ) : ZMod c) =
        (m : ZMod c) * ((ZMod.unitOfCoprime d (Finset.mem_filter.mp hd).2 : (ZMod c)ˣ) : ZMod c) +
          (n : ZMod c) * (((ZMod.unitOfCoprime d (Finset.mem_filter.mp hd).2)⁻¹ : (ZMod c)ˣ) :
            ZMod c) := by
      rw [← ZMod.inv_coe_unit]
      simp [ZMod.coe_unitOfCoprime]
    rw [← key, stdAddChar_intCast_eq_ee]
    push_cast; rfl

/-- `S(t a, b) = S(a, t b)` for a unit `t`. -/
theorem kl_mul_left_unit (c : ℕ) [NeZero c] (t : (ZMod c)ˣ) (a b : ZMod c) :
    kl c ((t : ZMod c) * a) b = kl c a ((t : ZMod c) * b) := by
  unfold kl
  refine Fintype.sum_equiv (Equiv.mulLeft t) _ _ (fun x => ?_)
  simp only [Equiv.coe_mulLeft, Units.val_mul, mul_inv_rev]
  congr 1
  have : ((t : ZMod c) * ((t⁻¹ : (ZMod c)ˣ) : ZMod c)) = 1 := by simp
  linear_combination (-(b * (((x⁻¹ : (ZMod c)ˣ)) : ZMod c))) * this

/-- `S(t, b) = S(1, t b)`. -/
theorem kl_unit_eq (c : ℕ) [NeZero c] (t : (ZMod c)ˣ) (b : ZMod c) :
    kl c t b = kl c 1 ((t : ZMod c) * b) := by
  have := kl_mul_left_unit c t 1 b
  rwa [mul_one] at this

/-! ### Twisted multiplicativity -/

section Mult

variable {q r : ℕ} [NeZero q] [NeZero r]

/-- `ψ_{qr}(y) = ψ_q(u ȳ) ψ_r(v ȳ)` when `u r + v q = 1`. -/
lemma stdAddChar_mul_split (u v : ℤ) (huv : u * r + v * q = 1) (y : ZMod (q * r)) :
    haveI : NeZero (q * r) := ⟨mul_ne_zero (NeZero.ne q) (NeZero.ne r)⟩
    ZMod.stdAddChar y =
      ZMod.stdAddChar ((u : ZMod q) * ZMod.castHom (Dvd.intro r rfl) (ZMod q) y) *
        ZMod.stdAddChar ((v : ZMod r) * ZMod.castHom (Dvd.intro_left q rfl) (ZMod r) y) := by
  haveI : NeZero (q * r) := ⟨mul_ne_zero (NeZero.ne q) (NeZero.ne r)⟩
  obtain ⟨Y, rfl⟩ : ∃ Y : ℤ, (Y : ZMod (q * r)) = y := ⟨y.val, by simp [ZMod.natCast_zmod_val]⟩
  simp only [map_intCast]
  rw [← Int.cast_mul, ← Int.cast_mul, stdAddChar_intCast_eq_ee, stdAddChar_intCast_eq_ee,
    stdAddChar_intCast_eq_ee, ee, ee, ee, ← Complex.exp_add]
  congr 1
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hr : (r : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne r
  have huv' : (u : ℂ) * r + (v : ℂ) * q = 1 := by exact_mod_cast huv
  push_cast
  field_simp
  linear_combination (-(Y : ℂ)) * huv'

/-- The CRT equivalence on units. -/
noncomputable def unitsCRT (h : q.Coprime r) : (ZMod (q * r))ˣ ≃* (ZMod q)ˣ × (ZMod r)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits

lemma unitsCRT_fst (h : q.Coprime r) (w : (ZMod (q * r))ˣ) :
    (((unitsCRT h w).1 : (ZMod q)ˣ) : ZMod q) =
      ZMod.castHom (Dvd.intro r rfl) (ZMod q) (w : ZMod (q * r)) := by
  simp [unitsCRT, MulEquiv.prodUnits, ZMod.chineseRemainder]

lemma unitsCRT_snd (h : q.Coprime r) (w : (ZMod (q * r))ˣ) :
    (((unitsCRT h w).2 : (ZMod r)ˣ) : ZMod r) =
      ZMod.castHom (Dvd.intro_left q rfl) (ZMod r) (w : ZMod (q * r)) := by
  simp [unitsCRT, MulEquiv.prodUnits, ZMod.chineseRemainder]

/-- **Twisted multiplicativity** of Kloosterman sums. -/
theorem kl_mul_coprime (h : q.Coprime r) (u v : ℤ) (huv : u * r + v * q = 1) (m n : ℤ) :
    haveI : NeZero (q * r) := ⟨mul_ne_zero (NeZero.ne q) (NeZero.ne r)⟩
    kl (q * r) m n = kl q (u * m) (u * n) * kl r (v * m) (v * n) := by
  haveI : NeZero (q * r) := ⟨mul_ne_zero (NeZero.ne q) (NeZero.ne r)⟩
  unfold kl
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (unitsCRT h) _ _ (fun w => ?_)
  rw [stdAddChar_mul_split u v huv]
  have h1 := unitsCRT_fst h w
  have h2 := unitsCRT_snd h w
  have h1' := unitsCRT_fst h w⁻¹
  have h2' := unitsCRT_snd h w⁻¹
  rw [map_inv] at h1' h2'
  simp only [Prod.fst_inv, Prod.snd_inv] at h1' h2'
  simp only [map_add, map_mul, map_intCast]
  erw [h1, h2, h1', h2']
  ring_nf

end Mult

end RamanujanTau.TauBound
