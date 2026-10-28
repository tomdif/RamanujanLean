import RamanujanTau.TateCurve.Basic
import RamanujanTau.TateCurve.VonStaudt
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# The Hasse-invariant lift `E_{p−1}` and `E_{p−1} ≡ 1 (mod p)`

`Eis k = 1 − (2k / B_k) Σ_{n≥1} σ_{k−1}(n) qⁿ ∈ ℚ⟦q⟧`. For a prime `p ≥ 5` (in fact `p ≥ 3`), every coefficient
of `E_{p−1} − 1` has `p`-adic norm `≤ p⁻¹`, and `E_{p−1}` lifts to `ℤ_[p]⟦q⟧` with reduction `1` in `𝔽_p⟦q⟧`.
-/

set_option autoImplicit false

namespace TateCurve
open PowerSeries
open scoped ArithmeticFunction.sigma

/-- The constant `−2k/B_k` (so that `Eis k = 1 + κ_k Σ σ_{k−1}(n) qⁿ`). -/
noncomputable def kappa (k : ℕ) : ℚ := -(2 * (k : ℚ) / bernoulli k)

/-- The normalized Eisenstein series `E_k = 1 − (2k/B_k) Σ_{n ≥ 1} σ_{k−1}(n) qⁿ` as a formal series over `ℚ`. -/
noncomputable def Eis (k : ℕ) : PowerSeries ℚ :=
  1 - C (2 * (k : ℚ) / bernoulli k) * map (Int.castRingHom ℚ) (s (k - 1))

/-- The Hasse-invariant lift `E_{p−1}`. -/
noncomputable abbrev Ehasse (p : ℕ) : PowerSeries ℚ := Eis (p - 1)

lemma coeff_Eis (k n : ℕ) :
    coeff n (Eis k) = (if n = 0 then 1 else 0) + kappa k * (σ (k - 1) n : ℚ) := by
  rw [Eis, map_sub, coeff_one, coeff_C_mul, coeff_map, coeff_s, kappa, eq_intCast]
  push_cast
  ring

lemma coeff_Eis_sub_one (k n : ℕ) :
    coeff n (Eis k - 1) = kappa k * (σ (k - 1) n : ℚ) := by
  rw [map_sub, coeff_Eis, coeff_one]; ring

lemma bernoulli_four' : bernoulli 4 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]

lemma bernoulli_six : bernoulli 6 = 1 / 42 := by
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd ⟨2, rfl⟩ (by norm_num)
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four, h5]
  norm_num [Nat.choose]

/-- `E₄ = 1 + 240 s₃`: the general `Eis` agrees with `c₄(Tate)`. -/
theorem Eis_four : Eis 4 = map (Int.castRingHom ℚ) Tate.c₄ := by
  ext n
  rw [coeff_Eis, kappa, bernoulli_four', c₄_Tate, coeff_map, map_add, coeff_one,
    show (240 : PowerSeries ℤ) = ((240 : ℤ) : PowerSeries ℤ) by norm_cast, coeff_ofInt_mul, coeff_s]
  simp only [eq_intCast]
  push_cast
  norm_num

/-- `E₆ = 1 − 504 s₅ = −c₆(Tate)`. -/
theorem Eis_six : Eis 6 = map (Int.castRingHom ℚ) (-Tate.c₆) := by
  ext n
  rw [coeff_Eis, kappa, bernoulli_six, c₆_Tate, neg_neg, coeff_map, map_sub, coeff_one,
    show (504 : PowerSeries ℤ) = ((504 : ℤ) : PowerSeries ℤ) by norm_cast, coeff_ofInt_mul, coeff_s]
  simp only [eq_intCast]
  push_cast
  norm_num
  ring

section prime
variable {p : ℕ} [hp : Fact p.Prime]

/-- `|κ_{p−1}|_p = p⁻¹`, i.e. `2(p−1)/B_{p−1} ∈ p ℤ_(p)` exactly. -/
theorem padicNorm_kappa (hp3 : 3 ≤ p) : padicNorm p (kappa (p - 1)) = (p : ℚ)⁻¹ := by
  have hB := padicNorm_p_mul_bernoulli_eq_one (p := p) hp3
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hB0 : bernoulli (p - 1) ≠ 0 := bernoulli_sub_one_ne_zero hp3
  have hrw : kappa (p - 1) = -(((2 * (p - 1) : ℕ) : ℚ) * (p : ℚ) / ((p : ℚ) * bernoulli (p - 1))) := by
    rw [kappa]
    congr 1
    rw [Nat.cast_mul, Nat.cast_ofNat]
    field_simp
  have h2 : padicNorm p (((2 * (p - 1) : ℕ) : ℚ)) = 1 := by
    rw [padicNorm.nat_eq_one_iff]
    intro hd
    rcases (Nat.Prime.dvd_mul hp.out).mp hd with h | h
    · have := Nat.le_of_dvd (by norm_num) h; omega
    · have := Nat.le_of_dvd (by omega) h; omega
  rw [hrw, padicNorm.neg, padicNorm.div, padicNorm.mul, h2, hB, padicNorm.padicNorm_p_of_prime]
  ring

/-- **`E_{p−1} ≡ 1 (mod p)`**: every coefficient of `E_{p−1} − 1` lies in `p ℤ_(p)`. -/
theorem padicNorm_coeff_Ehasse_sub_one (hp3 : 3 ≤ p) (n : ℕ) :
    padicNorm p (coeff n (Ehasse p - 1)) ≤ (p : ℚ)⁻¹ := by
  rw [Ehasse, coeff_Eis_sub_one, padicNorm.mul, padicNorm_kappa hp3]
  exact mul_le_of_le_one_right (by positivity) (padicNorm_natCast_le _)

/-- The coefficients of `E_{p−1}` are `p`-integral. -/
theorem padicNorm_coeff_Ehasse_le_one (hp3 : 3 ≤ p) (n : ℕ) :
    padicNorm p (coeff n (Ehasse p)) ≤ 1 := by
  have h1 := padicNorm_coeff_Ehasse_sub_one hp3 n
  have hle : (p : ℚ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_lt.le)
  calc padicNorm p (coeff n (Ehasse p)) = padicNorm p (coeff n (Ehasse p - 1) + coeff n (1 : PowerSeries ℚ)) := by
        rw [map_sub, sub_add_cancel]
    _ ≤ max _ _ := padicNorm.nonarchimedean
    _ ≤ 1 := max_le (h1.trans hle) (by rw [coeff_one]; split_ifs <;> simp)

/-- `E_{p−1}` as a power series over `ℤ_[p]`. -/
noncomputable def EhasseZp (p : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p) : PowerSeries ℤ_[p] :=
  mk fun n => ⟨((coeff n (Ehasse p) : ℚ) : ℚ_[p]), by
    rw [Padic.eq_padicNorm]; exact_mod_cast padicNorm_coeff_Ehasse_le_one hp3 n⟩

/-- `EhasseZp` is the image of `E_{p−1}` in `ℚ_[p]⟦q⟧`. -/
theorem map_EhasseZp (hp3 : 3 ≤ p) :
    map (PadicInt.Coe.ringHom (p := p)) (EhasseZp p hp3) = map (Rat.castHom ℚ_[p]) (Ehasse p) := by
  ext n
  simp [EhasseZp, coeff_map]

/-- **`E_{p−1} ≡ 1 (mod p)`** in `𝔽_p⟦q⟧`. -/
theorem map_toZMod_EhasseZp (hp3 : 3 ≤ p) : map (PadicInt.toZMod (p := p)) (EhasseZp p hp3) = 1 := by
  ext n
  rw [coeff_map, coeff_one]
  -- write the coefficient as `1_{n=0} + (small)`
  set z : ℤ_[p] := coeff n (EhasseZp p hp3) with hz
  have hsmall : z - (if n = 0 then 1 else 0) ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
    have hval : ((z - (if n = 0 then 1 else 0) : ℤ_[p]) : ℚ_[p]) = ((coeff n (Ehasse p - 1) : ℚ) : ℚ_[p]) := by
      rw [hz, EhasseZp, coeff_mk, map_sub, coeff_one]
      split_ifs <;> simp
    rw [PadicInt.norm_def, hval, Padic.eq_padicNorm]
    have := padicNorm_coeff_Ehasse_sub_one hp3 n
    have hlt : (p : ℚ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
    exact_mod_cast lt_of_le_of_lt this hlt
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, sub_eq_zero] at hsmall
  rw [hsmall]
  split_ifs <;> simp

end prime

end TateCurve
