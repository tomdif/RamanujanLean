/-
# Ramanujan's congruence `τ(n) ≡ σ₁₁(n) (mod 691)` — the modular-forms argument

Weight-12 level-one modular forms `M₁₂` are 2-dimensional. Both `E₄³` and the normalized weight-12
Eisenstein series `E₁₂` have constant term `1`, so `E₄³ − E₁₂` has constant term `0` and is therefore a cusp
form, hence a scalar multiple of `Δ`. Matching the `q¹` coefficient (`E₄³`: `720`, `E₁₂`: `65520/691`,
`Δ`: `τ(1)=1`) gives

  `E₄³ = E₁₂ + (432000/691)·Δ`.

Reading off the `qⁿ` coefficient (`n ≥ 1`): `a(n) = (65520/691)σ₁₁(n) + (432000/691)τ(n)` where `a(n)` is an
integer (`E₄³` has integer q-expansion). Since `65520 + 432000 = 720·691`, clearing `691` gives
`432000(τ(n) − σ₁₁(n)) ≡ 0 (mod 691)`, and `691 ∤ 432000` yields `τ(n) ≡ σ₁₁(n) (mod 691)`.

This file formalizes the argument on Mathlib's modular-forms library and proves the congruence
**unconditionally** (`tau_congruence_mod691_unconditional`): the `M₁₂` relation `E₄³ = E₁₂ + (432000/691)·Δ`
gives the arithmetic heart, and integrality `τ(n) ∈ ℤ` (`tau_int`) is proved from `1728 ∣ [qⁿ](p₄³ − p₆²)`.
-/
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.DimensionFormulas.LevelOne
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.NormNum.Prime
import RamanujanTau.DiscriminantBridge

namespace RamanujanTau.Mod691

open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane
open scoped MatrixGroups ArithmeticFunction.sigma
open RamanujanTau.DiscriminantBridge (Δmod coeff_one_discriminant)

/-- The normalized weight-12 Eisenstein series `E₁₂` for `SL₂(ℤ)`. -/
noncomputable def E12 := E (show 3 ≤ 12 by norm_num)

/-- `B₁₂ = −691/2730`. -/
lemma bernoulli_twelve : bernoulli 12 = -691 / 2730 := by decide +kernel

/-- **Milestone 1: the `E₁₂` q-expansion carries `691`.** For `m ≥ 1`,
`(E₁₂)_m = (65520/691)·σ₁₁(m)`. -/
lemma E12_qExpansion_coeff {m : ℕ} (hm : m ≠ 0) :
    (qExpansion 1 E12).coeff m = (65520 / 691 : ℂ) * (σ 11 m : ℂ) := by
  rw [E12, E_qExpansion_coeff (show 3 ≤ 12 by norm_num) (by decide) m, if_neg hm,
      bernoulli_twelve]
  norm_num

/-! ### Milestone 2: the `E₄³` q-expansion (constant term `1`, `q¹`-coefficient `720`) -/

/-- `E₄`'s q-expansion constant term is `1`. -/
lemma qE4_coeff_zero : (qExpansion 1 E₄).coeff 0 = 1 := E_qExpansion_coeff_zero _ ⟨2, rfl⟩

/-- `E₄³` has constant term `1`. -/
lemma qE4cube_coeff_zero : ((qExpansion 1 E₄) ^ 3).coeff 0 = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff,
      qE4_coeff_zero, one_pow]

/-- `E₄³` has `q¹`-coefficient `720 = 3·240`. -/
lemma qE4cube_coeff_one : ((qExpansion 1 E₄) ^ 3).coeff 1 = 720 := by
  have h0 := qE4_coeff_zero
  have h1 : (qExpansion 1 E₄).coeff 1 = 240 := E₄_qExpansion_coeff_one
  have hp2_0 : ((qExpansion 1 E₄) ^ 2).coeff 0 = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff,
        h0, one_pow]
  have hp2_1 : ((qExpansion 1 E₄) ^ 2).coeff 1 = 480 := by
    rw [pow_two, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.sum_range_succ, Finset.sum_range_one, h0, h1]
    ring
  rw [pow_succ, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, Finset.sum_range_one, hp2_0, hp2_1, h0, h1]
  ring

/-! ### Milestone 3: the `M₁₂` linear relation `E₄³ = E₁₂ + (432000/691)·Δ`

`E₄³` (weight `4+4+4 = 12`) and the cusp function `Δ` live in the 2-dimensional space `M₁₂`. Since `E₄³ − E₁₂`
has constant term `0` it is a cusp form, hence `= c·Δ` by `exists_smul_discriminant_of_weight_eq_twelve`;
matching `q¹` coefficients (`E₄³ : 720`, `E₁₂ : 65520/691`, `Δ : τ(1) = 1` via `coeff_one_discriminant`)
pins `c = 720 − 65520/691 = 432000/691`. -/

/-- `E₄³` as a weight-12 modular form (`4 + 4 + 4 = 12`). -/
noncomputable def E4cube : ModularForm 𝒮ℒ 12 := (E₄.mul E₄).mul E₄

lemma coe_E4cube : (E4cube : ℍ → ℂ) = (E₄ : ℍ → ℂ) * (E₄ : ℍ → ℂ) * (E₄ : ℍ → ℂ) := by
  show (((E₄.mul E₄).mul E₄ : ModularForm 𝒮ℒ 12) : ℍ → ℂ) = _
  rw [ModularForm.coe_mul, ModularForm.coe_mul]

/-- The q-expansion of the modular form `E₄³` is the cube of the q-expansion of `E₄`. -/
lemma qExpansion_E4cube : qExpansion 1 E4cube = (qExpansion 1 E₄) ^ 3 := by
  have hA : AnalyticAt ℂ (cuspFunction 1 (E₄ : ℍ → ℂ)) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero E₄ one_pos one_mem_strictPeriods_SL
  have hA2 : AnalyticAt ℂ (cuspFunction 1 ((E₄:ℍ→ℂ) * (E₄:ℍ→ℂ))) 0 := by
    have := ModularFormClass.analyticAt_cuspFunction_zero (E₄.mul E₄) one_pos one_mem_strictPeriods_SL
    rwa [ModularForm.coe_mul] at this
  rw [congrArg (qExpansion 1) coe_E4cube, UpperHalfPlane.qExpansion_mul hA2 hA,
      UpperHalfPlane.qExpansion_mul hA hA]
  ring

/-- **`E₄³ − E₁₂` is a scalar multiple of `Δ`** (both are weight-12; the difference is a cusp form). -/
lemma exists_smul_disc :
    ∃ c : ℂ, c • qExpansion 1 Δmod = qExpansion 1 E4cube - qExpansion 1 E12 := by
  have h4 : (qExpansion 1 E₄).coeff 0 = 1 := E_qExpansion_coeff_zero _ ⟨2, rfl⟩
  have h12 : (qExpansion 1 E12).coeff 0 = 1 := E_qExpansion_coeff_zero _ ⟨6, rfl⟩
  have hcoeff0 : (qExpansion 1 (E4cube - E12)).coeff 0 = 0 := by
    rw [ModularFormClass.qExpansion_sub one_pos one_mem_strictPeriods_SL E4cube E12, map_sub,
        qExpansion_E4cube, PowerSeries.coeff_zero_eq_constantCoeff, map_pow,
        ← PowerSeries.coeff_zero_eq_constantCoeff, h4, one_pow, h12, sub_self]
  set gc : CuspForm 𝒮ℒ 12 := ModularForm.toCuspForm (E4cube - E12) hcoeff0 with hgc
  obtain ⟨c, hc⟩ := CuspForm.exists_smul_discriminant_of_weight_eq_twelve gc
  refine ⟨c, ?_⟩
  have hΔ : (Δmod : ℍ → ℂ) = (CuspForm.discriminant : ℍ → ℂ) := rfl
  have hAΔ : AnalyticAt ℂ (cuspFunction 1 (Δmod : ℍ → ℂ)) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero Δmod one_pos one_mem_strictPeriods_SL
  have hfun : ((c • CuspForm.discriminant : CuspForm 𝒮ℒ 12) : ℍ → ℂ)
      = ((E4cube - E12 : ModularForm 𝒮ℒ 12) : ℍ → ℂ) := by
    rw [hc]; ext z; simp only [hgc, ModularForm.toCuspForm_apply]
  calc c • qExpansion 1 Δmod
      = qExpansion 1 (c • (Δmod : ℍ → ℂ)) := (UpperHalfPlane.qExpansion_smul hAΔ c).symm
    _ = qExpansion 1 ((c • CuspForm.discriminant : CuspForm 𝒮ℒ 12) : ℍ → ℂ) := rfl
    _ = qExpansion 1 ((E4cube - E12 : ModularForm 𝒮ℒ 12) : ℍ → ℂ) := by rw [hfun]
    _ = qExpansion 1 E4cube - qExpansion 1 E12 :=
        ModularFormClass.qExpansion_sub one_pos one_mem_strictPeriods_SL E4cube E12

/-- **The arithmetic heart of Ramanujan's mod-691 congruence.** For `n ≥ 1`, the `qⁿ`-coefficients of the
weight-12 relation `E₄³ = E₁₂ + (432000/691)·Δ` satisfy

  `691·[qⁿ]E₄³ = 65520·σ₁₁(n) + 432000·τ(n)`,   where `τ(n) = [qⁿ] qExpansion(Δ)`.

Since `65520 + 432000 = 720·691`, this says `65520·σ₁₁(n) + 432000·τ(n) ≡ 0 (mod 691)`; as `65520 ≡ −432000`
and `691 ∤ 432000`, that is exactly `τ(n) ≡ σ₁₁(n) (mod 691)` — *once* `τ(n)` and `[qⁿ]E₄³` are known to be
integers (Mathlib does not yet carry integrality of the `η²⁴` q-expansion). -/
theorem tau_mod_relation {n : ℕ} (hn : n ≠ 0) :
    691 * ((qExpansion 1 E₄) ^ 3).coeff n
      = 65520 * (σ 11 n : ℂ) + 432000 * (qExpansion 1 Δmod).coeff n := by
  obtain ⟨c, hc⟩ := exists_smul_disc
  have hc1 := congrArg (fun p => PowerSeries.coeff 1 p) hc
  simp only [PowerSeries.coeff_smul, map_sub, qExpansion_E4cube, smul_eq_mul,
    coeff_one_discriminant] at hc1
  have hq4 : ((qExpansion 1 E₄) ^ 3).coeff 1 = 720 := qE4cube_coeff_one
  rw [hq4, mul_one, E12_qExpansion_coeff one_ne_zero] at hc1
  have hcval : c = 432000 / 691 := by rw [hc1]; norm_num
  have hcn := congrArg (fun p => PowerSeries.coeff n p) hc
  simp only [PowerSeries.coeff_smul, map_sub, qExpansion_E4cube, smul_eq_mul,
    E12_qExpansion_coeff hn, hcval] at hcn
  linear_combination -691 * hcn

/-! ### The discriminant identity `E₄³ − E₆² = 1728·Δ`

The same weight-12 machinery, with `E₆²` in place of `E₁₂`, yields the classical closed form of `Δ`. Here the
scalar pins to `1728` (from `[q¹]E₄³ = 720`, `[q¹]E₆² = 2·(−504) = −1008`), and the identity holds as a full
power-series equality — every coefficient, including the constant term. -/

/-- `E₆²` as a weight-12 modular form (`6 + 6 = 12`). -/
noncomputable def E6sq : ModularForm 𝒮ℒ 12 := E₆.mul E₆

lemma coe_E6sq : (E6sq : ℍ → ℂ) = (E₆ : ℍ → ℂ) * (E₆ : ℍ → ℂ) := by
  show ((E₆.mul E₆ : ModularForm 𝒮ℒ 12) : ℍ → ℂ) = _
  rw [ModularForm.coe_mul]

/-- The q-expansion of `E₆²` is the square of the q-expansion of `E₆`. -/
lemma qExpansion_E6sq : qExpansion 1 E6sq = (qExpansion 1 E₆) ^ 2 := by
  have hA : AnalyticAt ℂ (cuspFunction 1 (E₆ : ℍ → ℂ)) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero E₆ one_pos one_mem_strictPeriods_SL
  rw [congrArg (qExpansion 1) coe_E6sq, UpperHalfPlane.qExpansion_mul hA hA, sq]

lemma qE6sq_coeff_zero : ((qExpansion 1 E₆) ^ 2).coeff 0 = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff,
      E_qExpansion_coeff_zero (show 3 ≤ 6 by norm_num) ⟨3, rfl⟩, one_pow]

lemma qE6sq_coeff_one : ((qExpansion 1 E₆) ^ 2).coeff 1 = -1008 := by
  have h0 : (qExpansion 1 E₆).coeff 0 = 1 := E_qExpansion_coeff_zero _ ⟨3, rfl⟩
  rw [pow_two, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, Finset.sum_range_one, h0, E₆_qExpansion_coeff_one]
  ring

/-- **The discriminant identity** `E₄³ − E₆² = 1728·Δ`, as an equality of q-expansions. Coefficient-wise,
`[qⁿ]E₄³ − [qⁿ]E₆² = 1728·τ(n)` for every `n`. -/
theorem qExpansion_E4cube_sub_E6sq :
    qExpansion 1 E4cube - qExpansion 1 E6sq = (1728 : ℂ) • qExpansion 1 Δmod := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c • qExpansion 1 Δmod = qExpansion 1 E4cube - qExpansion 1 E6sq := by
    have h4 : (qExpansion 1 E₄).coeff 0 = 1 := E_qExpansion_coeff_zero _ ⟨2, rfl⟩
    have h6 : (qExpansion 1 E₆).coeff 0 = 1 := E_qExpansion_coeff_zero _ ⟨3, rfl⟩
    have hcoeff0 : (qExpansion 1 (E4cube - E6sq)).coeff 0 = 0 := by
      rw [ModularFormClass.qExpansion_sub one_pos one_mem_strictPeriods_SL E4cube E6sq, map_sub,
          qExpansion_E4cube, qExpansion_E6sq, qE4cube_coeff_zero, qE6sq_coeff_zero, sub_self]
    set gc : CuspForm 𝒮ℒ 12 := ModularForm.toCuspForm (E4cube - E6sq) hcoeff0 with hgc
    obtain ⟨c, hc⟩ := CuspForm.exists_smul_discriminant_of_weight_eq_twelve gc
    refine ⟨c, ?_⟩
    have hΔ : (Δmod : ℍ → ℂ) = (CuspForm.discriminant : ℍ → ℂ) := rfl
    have hAΔ : AnalyticAt ℂ (cuspFunction 1 (Δmod : ℍ → ℂ)) 0 :=
      ModularFormClass.analyticAt_cuspFunction_zero Δmod one_pos one_mem_strictPeriods_SL
    have hfun : ((c • CuspForm.discriminant : CuspForm 𝒮ℒ 12) : ℍ → ℂ)
        = ((E4cube - E6sq : ModularForm 𝒮ℒ 12) : ℍ → ℂ) := by
      rw [hc]; ext z; simp only [hgc, ModularForm.toCuspForm_apply]
    calc c • qExpansion 1 Δmod
        = qExpansion 1 (c • (Δmod : ℍ → ℂ)) := (UpperHalfPlane.qExpansion_smul hAΔ c).symm
      _ = qExpansion 1 ((c • CuspForm.discriminant : CuspForm 𝒮ℒ 12) : ℍ → ℂ) := rfl
      _ = qExpansion 1 ((E4cube - E6sq : ModularForm 𝒮ℒ 12) : ℍ → ℂ) := by rw [hfun]
      _ = qExpansion 1 E4cube - qExpansion 1 E6sq :=
          ModularFormClass.qExpansion_sub one_pos one_mem_strictPeriods_SL E4cube E6sq
  have hc1 := congrArg (fun p => PowerSeries.coeff 1 p) hc
  simp only [PowerSeries.coeff_smul, map_sub, qExpansion_E4cube, qExpansion_E6sq, smul_eq_mul,
    coeff_one_discriminant, qE4cube_coeff_one, qE6sq_coeff_one] at hc1
  have hcval : c = 1728 := by linear_combination hc1
  rw [← hc, hcval]

/-- Coefficient form of the discriminant identity: `1728·τ(n) = [qⁿ]E₄³ − [qⁿ]E₆²` for every `n`. -/
theorem tau_smul_eq_coeff (n : ℕ) :
    (1728 : ℂ) * (qExpansion 1 Δmod).coeff n
      = ((qExpansion 1 E₄) ^ 3).coeff n - ((qExpansion 1 E₆) ^ 2).coeff n := by
  have h := congrArg (fun p => PowerSeries.coeff n p) qExpansion_E4cube_sub_E6sq
  simpa only [map_sub, PowerSeries.coeff_smul, qExpansion_E4cube, qExpansion_E6sq, smul_eq_mul]
    using h.symm

/-! ### Integrality of `E₄`, `E₆`, and of `τ` — closing the congruence unconditionally

`E₄ = 1 + 240·∑σ₃(n)qⁿ` and `E₆ = 1 − 504·∑σ₅(n)qⁿ` are the images under `ℤ ↪ ℂ` of explicit integer series
`p₄`, `p₆`. Since `1728·τ(n) = [qⁿ](E₄³ − E₆²) = [qⁿ](p₄³ − p₆²)` (cast to ℂ), integrality of `τ` reduces to
`1728 ∣ [qⁿ](p₄³ − p₆²)`. Expanding, the `A²,A³,B²` terms carry an explicit factor `1728`, and the linear
term is `144·(5σ₃(n) + 7σ₅(n))` with `12 ∣ 5σ₃+7σ₅` — which holds since `12 ∣ 5d³ + 7d⁵` for every divisor
`d` (decidable in `ZMod 12`). This proves `τ(n) ∈ ℤ`, discharging the last hypothesis. -/

/-- Power series over `ℂ` with integer coefficients: the image of `PowerSeries ℤ`. -/
noncomputable def intSeries : Subring (PowerSeries ℂ) := (PowerSeries.map (Int.castRingHom ℂ)).range

lemma coeff_int_of_mem {p : PowerSeries ℂ} (hp : p ∈ intSeries) (n : ℕ) :
    ∃ z : ℤ, PowerSeries.coeff n p = (z : ℂ) := by
  obtain ⟨q, hq⟩ := hp
  exact ⟨PowerSeries.coeff n q, by rw [← hq, PowerSeries.coeff_map]; rfl⟩

/-- `∑ σ₃(n) qⁿ` and `∑ σ₅(n) qⁿ` over `ℤ`, and the integer preimages `p₄ = 1 + 240·∑σ₃`, `p₆ = 1 − 504·∑σ₅`
of the `E₄`, `E₆` q-expansions. -/
noncomputable def sig3 : PowerSeries ℤ := PowerSeries.mk (fun n => (σ 3 n : ℤ))
noncomputable def sig5 : PowerSeries ℤ := PowerSeries.mk (fun n => (σ 5 n : ℤ))
noncomputable def p4 : PowerSeries ℤ := 1 + 240 * sig3
noncomputable def p6 : PowerSeries ℤ := 1 - 504 * sig5

lemma coeff_intCast_mul (k : ℤ) (Y : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n ((k : PowerSeries ℤ) * Y) = k * PowerSeries.coeff n Y := by
  rw [← zsmul_eq_mul, map_smul, smul_eq_mul]

lemma coeff_p4 (n : ℕ) : PowerSeries.coeff n p4 = if n = 0 then 1 else 240 * (σ 3 n : ℤ) := by
  rw [p4, map_add, PowerSeries.coeff_one,
      show (240 : PowerSeries ℤ) = ((240 : ℤ) : PowerSeries ℤ) by push_cast; ring,
      coeff_intCast_mul, sig3, PowerSeries.coeff_mk]
  by_cases h : n = 0 <;> simp [h]

lemma coeff_p6 (n : ℕ) : PowerSeries.coeff n p6 = if n = 0 then 1 else -504 * (σ 5 n : ℤ) := by
  rw [p6, map_sub, PowerSeries.coeff_one,
      show (504 : PowerSeries ℤ) = ((504 : ℤ) : PowerSeries ℤ) by push_cast; ring,
      coeff_intCast_mul, sig5, PowerSeries.coeff_mk]
  by_cases h : n = 0 <;> simp [h]

lemma qExpansion_E4_eq : qExpansion 1 E₄ = PowerSeries.map (Int.castRingHom ℂ) p4 := by
  ext n
  rw [PowerSeries.coeff_map, coeff_p4, E_qExpansion_coeff (show 3 ≤ 4 by norm_num) ⟨2, rfl⟩ n]
  by_cases h : n = 0
  · simp [h]
  · rw [if_neg h, if_neg h, show bernoulli 4 = -1/30 from by decide +kernel]
    simp only [Int.coe_castRingHom]; push_cast; ring

lemma qExpansion_E6_eq : qExpansion 1 E₆ = PowerSeries.map (Int.castRingHom ℂ) p6 := by
  ext n
  rw [PowerSeries.coeff_map, coeff_p6, E_qExpansion_coeff (show 3 ≤ 6 by norm_num) ⟨3, rfl⟩ n]
  by_cases h : n = 0
  · simp [h]
  · rw [if_neg h, if_neg h, show bernoulli 6 = 1/42 from by decide +kernel]
    simp only [Int.coe_castRingHom]; push_cast; ring

lemma E4_mem_intSeries : qExpansion 1 E₄ ∈ intSeries := ⟨p4, qExpansion_E4_eq.symm⟩

/-- **`[qⁿ]E₄³ ∈ ℤ`** — `E₄` has integer q-expansion, and integer series are closed under products. -/
lemma E4cube_coeff_int (n : ℕ) : ∃ z : ℤ, ((qExpansion 1 E₄) ^ 3).coeff n = (z : ℂ) :=
  coeff_int_of_mem (pow_mem E4_mem_intSeries 3) n

/-- **`12 ∣ 5σ₃(n) + 7σ₅(n)`** — from `12 ∣ 5d³ + 7d⁵` for every divisor `d` (checked in `ZMod 12`). -/
lemma sigma_dvd (n : ℕ) : (12 : ℤ) ∣ 5 * (σ 3 n : ℤ) + 7 * (σ 5 n : ℤ) := by
  have hpt : ∀ d : ℤ, (12 : ℤ) ∣ 5 * d ^ 3 + 7 * d ^ 5 := by
    intro d
    have h : ∀ x : ZMod 12, 5 * x ^ 3 + 7 * x ^ 5 = 0 := by decide
    have hz : ((5 * d ^ 3 + 7 * d ^ 5 : ℤ) : ZMod 12) = 0 := by push_cast; exact h _
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 12).mp hz
  rw [ArithmeticFunction.sigma_apply, ArithmeticFunction.sigma_apply]
  push_cast [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  exact Finset.dvd_sum (fun d _ => hpt _)

/-- **`1728 ∣ [qⁿ](p₄³ − p₆²)`** — the classical integrality of `Δ = (E₄³ − E₆²)/1728`. -/
theorem key_dvd (n : ℕ) : (1728 : ℤ) ∣ PowerSeries.coeff n (p4 ^ 3 - p6 ^ 2) := by
  have hexp : p4 ^ 3 - p6 ^ 2
      = 144 * (5 * sig3 + 7 * sig5) + 1728 * (100 * sig3 ^ 2 + 8000 * sig3 ^ 3 - 147 * sig5 ^ 2) := by
    rw [p4, p6]; ring
  rw [hexp, map_add,
      show (144 : PowerSeries ℤ) = ((144 : ℤ) : PowerSeries ℤ) by push_cast; ring, coeff_intCast_mul,
      show (1728 : PowerSeries ℤ) = ((1728 : ℤ) : PowerSeries ℤ) by push_cast; ring, coeff_intCast_mul,
      map_add,
      show (5 : PowerSeries ℤ) = ((5 : ℤ) : PowerSeries ℤ) by push_cast; ring, coeff_intCast_mul,
      show (7 : PowerSeries ℤ) = ((7 : ℤ) : PowerSeries ℤ) by push_cast; ring, coeff_intCast_mul,
      sig3, sig5, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  obtain ⟨k, hk⟩ := sigma_dvd n
  refine Dvd.dvd.add ⟨k, by rw [hk]; ring⟩ ⟨_, rfl⟩

/-- **`τ(n) ∈ ℤ`** — integrality of the `η²⁴` q-expansion, proved via `1728·τ(n) = [qⁿ](p₄³ − p₆²)` and
`key_dvd`. This discharges the final hypothesis of the mod-691 congruence. -/
theorem tau_int (n : ℕ) : ∃ z : ℤ, (qExpansion 1 Δmod).coeff n = (z : ℂ) := by
  obtain ⟨m, hm⟩ := key_dvd n
  refine ⟨m, mul_left_cancel₀ (show (1728 : ℂ) ≠ 0 by norm_num) ?_⟩
  rw [tau_smul_eq_coeff]
  have e4 : ((qExpansion 1 E₄) ^ 3).coeff n = ((PowerSeries.coeff n (p4 ^ 3) : ℤ) : ℂ) := by
    rw [qExpansion_E4_eq, ← map_pow, PowerSeries.coeff_map]; rfl
  have e6 : ((qExpansion 1 E₆) ^ 2).coeff n = ((PowerSeries.coeff n (p6 ^ 2) : ℤ) : ℂ) := by
    rw [qExpansion_E6_eq, ← map_pow, PowerSeries.coeff_map]; rfl
  rw [e4, e6, ← Int.cast_sub, ← map_sub, hm]; push_cast; ring

/-! ### The literal congruence `τ(n) ≡ σ₁₁(n) (mod 691)`

`tau_mod_relation` is an identity in `ℂ`. Read in `ZMod 691` over the integer coefficients (`[qⁿ]E₄³ ∈ ℤ` and
`τ(n) ∈ ℤ`, both now proved), `65520 + 432000 = 720·691` forces `691 ∣ 65520·σ₁₁(n) + 432000·τ(n)`, and
`691 ∤ 432000` cancels to `τ(n) ≡ σ₁₁(n) (mod 691)`. `tau_congruence_mod691` states this for the integer
`t` with `τ(n) = t`; `tau_congruence_mod691_unconditional` supplies that `t` from `tau_int`. -/
theorem tau_congruence_mod691 {n : ℕ} (hn : n ≠ 0)
    {t : ℤ} (hτ : (qExpansion 1 Δmod).coeff n = (t : ℂ)) :
    (t : ZMod 691) = (σ 11 n : ZMod 691) := by
  obtain ⟨e, hE⟩ := E4cube_coeff_int n
  have hrel := tau_mod_relation hn
  rw [hE, hτ] at hrel
  -- transport the ℂ-identity to an ℤ-identity via injectivity of `ℤ → ℂ`
  have hZ : (691 : ℤ) * e = 65520 * (σ 11 n : ℤ) + 432000 * t := by
    have h : ((691 * e : ℤ) : ℂ) = ((65520 * (σ 11 n : ℤ) + 432000 * t : ℤ) : ℂ) := by
      push_cast; linear_combination hrel
    exact_mod_cast h
  -- `432000·(τ − σ) = 691·(…)`, and `691` is prime and coprime to `432000`
  have hp : Prime (691 : ℤ) := by norm_num
  have heq : 432000 * (t - (σ 11 n : ℤ)) = 691 * (e - 720 * (σ 11 n : ℤ)) := by
    linear_combination -hZ
  have hdvd : (691 : ℤ) ∣ 432000 * (t - (σ 11 n : ℤ)) := ⟨_, heq⟩
  have hnd : ¬ (691 : ℤ) ∣ 432000 := by norm_num
  have hdvd2 : (691 : ℤ) ∣ (t - (σ 11 n : ℤ)) := (hp.dvd_mul.mp hdvd).resolve_left hnd
  have hz : ((t - (σ 11 n : ℤ) : ℤ) : ZMod 691) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 691).mpr (by exact_mod_cast hdvd2)
  push_cast at hz
  linear_combination hz

/-- **Ramanujan's congruence, unconditionally.** For `n ≥ 1` there is an integer `τ(n)` equal to the `qⁿ`
coefficient of the modular discriminant's q-expansion, and `τ(n) ≡ σ₁₁(n) (mod 691)`. -/
theorem tau_congruence_mod691_unconditional (n : ℕ) (hn : n ≠ 0) :
    ∃ t : ℤ, (qExpansion 1 Δmod).coeff n = (t : ℂ) ∧ (t : ZMod 691) = (σ 11 n : ZMod 691) :=
  let ⟨t, ht⟩ := tau_int n
  ⟨t, ht, tau_congruence_mod691 hn ht⟩

/-- **Ramanujan's congruence in its iconic form:** for a prime `p`, `τ(p) ≡ 1 + p¹¹ (mod 691)`
(the case `σ₁₁(p) = 1 + p¹¹` of the general congruence). -/
theorem tau_prime_congruence_mod691 {p : ℕ} (hp : p.Prime) :
    ∃ t : ℤ, (qExpansion 1 Δmod).coeff p = (t : ℂ) ∧ (t : ZMod 691) = 1 + (p : ZMod 691) ^ 11 := by
  obtain ⟨t, ht, hcong⟩ := tau_congruence_mod691_unconditional p hp.pos.ne'
  refine ⟨t, ht, ?_⟩
  have hσ : σ 11 p = 1 + p ^ 11 := by
    have h := ArithmeticFunction.sigma_apply_prime_pow (k := 11) (i := 1) hp
    rw [pow_one] at h
    rw [h, Finset.sum_range_succ, Finset.sum_range_one]; norm_num
  rw [hcong, hσ]; push_cast; ring

end RamanujanTau.Mod691
