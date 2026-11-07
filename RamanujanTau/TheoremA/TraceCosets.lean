import RamanujanTau.TheoremA.BadPrimeModular
import Mathlib.NumberTheory.ModularForms.NormTrace

/-!
# Mathlib's trace along Γ₀(Mp) ⊂ Γ₀(M), as an explicit finite sum

For a prime `p` not dividing `M`, an explicit family of `p+1` matrices is a
complete set of coset representatives. Mathlib's actual trace of a form on
Γ₀(Mp) is therefore the sum of its slashes by those matrices. This one
computation serves both the Atkin–Lehner trace at a bad prime and the
construction of the good-prime Hecke operator.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA.TraceCosets
open Matrix CongruenceSubgroup ModularForm UpperHalfPlane
open scoped MatrixGroups ModularForm
open Subgroup (IsArithmetic)

variable {M N : ℕ}

instance gamma0_isFiniteRelIndex [NeZero N] (ℋ : Subgroup (GL (Fin 2) ℝ)) [ℋ.IsArithmetic] :
    (Gamma0 N : Subgroup (GL (Fin 2) ℝ)).IsFiniteRelIndex ℋ :=
  ⟨Subgroup.relIndex_ne_zero_trans (K := 𝒮ℒ)
    Subgroup.IsArithmetic.is_commensurable.1 Subgroup.IsArithmetic.is_commensurable.2⟩

/-- A family with `∃! i, r i * γ ∈ Γ₀(N)` for every γ computes Mathlib's trace. -/
theorem trace_eq_sum {ι : Type*} [Fintype ι] [NeZero N] [NeZero M] (r : ι → SL(2, ℤ))
    (hr : ∀ i, r i ∈ Gamma0 M)
    (hu : ∀ γ ∈ Gamma0 M, ∃! i, r i * γ ∈ Gamma0 N)
    {k : ℤ} (f : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    (ModularForm.trace (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) f : ℍ → ℂ) =
      ∑ i, (f : ℍ → ℂ) ∣[k] SpecialLinearGroup.mapGL ℝ (r i) := by
  classical
  let 𝒢 : Subgroup (GL (Fin 2) ℝ) := Gamma0 N
  let ℋ : Subgroup (GL (Fin 2) ℝ) := Gamma0 M
  let mem (γ : SL(2, ℤ)) (h : γ ∈ Gamma0 M) : ℋ := ⟨SpecialLinearGroup.mapGL ℝ γ, γ, h, rfl⟩
  let c : ι → ℋ ⧸ 𝒢.subgroupOf ℋ := fun i =>
    QuotientGroup.mk (mem (r i)⁻¹ (inv_mem (hr i)))
  have hmem : ∀ {γ : SL(2, ℤ)}, SpecialLinearGroup.mapGL ℝ γ ∈ 𝒢 → γ ∈ Gamma0 N := by
    rintro γ ⟨δ, hδ, he⟩
    have : δ = γ := by
      ext a b
      have := congrArg (fun g : GL (Fin 2) ℝ => g.val a b) he
      simpa using this
    exact this ▸ hδ
  have hbij : Function.Bijective c := by
    constructor
    · intro i j hij
      have h := QuotientGroup.eq.mp hij
      have h' : SpecialLinearGroup.mapGL ℝ (r i * (r j)⁻¹) ∈ 𝒢 := by
        have := Subgroup.mem_subgroupOf.mp h
        simpa [mem, map_mul, map_inv] using this
      obtain ⟨l, -, hl⟩ := hu (r j)⁻¹ (inv_mem (hr j))
      have hi := hl i (hmem h')
      have hj := hl j (by simpa using (Gamma0 N).one_mem)
      exact hi.trans hj.symm
    · intro q
      induction q using QuotientGroup.induction_on with
      | H h =>
        obtain ⟨_, γ, hγ, rfl⟩ := h
        obtain ⟨i, hi, -⟩ := hu γ hγ
        refine ⟨i, QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr ?_)⟩
        have : SpecialLinearGroup.mapGL ℝ (r i * γ) ∈ 𝒢 := ⟨_, hi, rfl⟩
        simpa [mem, map_mul, map_inv] using this
  letI := Fintype.ofFinite (ℋ ⧸ 𝒢.subgroupOf ℋ)
  rw [ModularForm.coe_trace]
  change ∑ q : ℋ ⧸ 𝒢.subgroupOf ℋ, SlashInvariantForm.quotientFunc f q = _
  rw [← (Equiv.ofBijective c hbij).sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [c, mem, Equiv.ofBijective, map_inv]

/-- The uniqueness hypothesis for representatives whose lower rows are `(1 : j)` up to a unit. -/
theorem existsUnique_coset {p : ℕ} [hp : Fact p.Prime] (hN : N = M * p)
    (r : Option (ZMod p) → SL(2, ℤ)) (u : ℤ)
    (hnone : r none = 1)
    (hu0 : ((u : ℤ) : ZMod p) ≠ 0) (hM : (M : ℤ) ∣ u)
    (hc : ∀ j, r (some j) 1 0 = u)
    (hd : ∀ j, (r (some j) 1 1 : ZMod p) = u * j)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    ∃! i, r i * γ ∈ Gamma0 N := by
  have hmem : ∀ δ : SL(2, ℤ), δ ∈ Gamma0 N ↔ ((N : ℤ) ∣ δ 1 0) := fun δ => by
    rw [Gamma0_mem]; exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _
  have hγM : (M : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
  have hpM : IsCoprime (M : ℤ) (p : ℤ) := by
    rw [isCoprime_comm, Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp.out)]
    intro h
    exact hu0 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (h.trans hM))
  have hcop : ∀ x : ℤ, (M : ℤ) ∣ x → (((N : ℤ) ∣ x) ↔ ((x : ℤ) : ZMod p) = 0) := by
    intro x hx
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hN]
    push_cast
    exact ⟨fun h => (dvd_mul_left _ _).trans h, fun h => hpM.mul_dvd hx h⟩
  have hnoneiff : r none * γ ∈ Gamma0 N ↔ (γ 1 0 : ZMod p) = 0 := by
    rw [hnone, one_mul, hmem, hcop _ hγM]
  have hsome : ∀ j, r (some j) * γ ∈ Gamma0 N ↔
      (u : ZMod p) * ((γ 0 0 : ZMod p) + j * γ 1 0) = 0 := by
    intro j
    have he : (r (some j) * γ) 1 0 = u * γ 0 0 + r (some j) 1 1 * γ 1 0 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, hc]
    rw [hmem, hcop _ (by rw [he]; exact dvd_add (hM.mul_right _) (hγM.mul_left _)), he]
    push_cast
    rw [hd]
    ring_nf
  have hdet : (γ 0 0 : ZMod p) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.property
    rw [det_fin_two] at h
    have h' := congrArg (Int.castRingHom (ZMod p)) h
    simpa using h'
  by_cases h0 : (γ 1 0 : ZMod p) = 0
  · refine ⟨none, hnoneiff.mpr h0, ?_⟩
    intro i hi
    cases i with
    | none => rfl
    | some j =>
      exfalso
      have := (hsome j).mp hi
      rw [h0, mul_zero, add_zero] at this
      have ha := (mul_eq_zero.mp this).resolve_left hu0
      rw [ha, h0] at hdet
      simp at hdet
  · refine ⟨some (-(γ 0 0 : ZMod p) / γ 1 0), (hsome _).mpr ?_, ?_⟩
    · field_simp
      ring
    · intro i hi
      cases i with
      | none => exact absurd (hnoneiff.mp hi) h0
      | some j =>
        have := (mul_eq_zero.mp ((hsome j).mp hi)).resolve_left hu0
        congr 1
        field_simp
        linear_combination this

/-- Integer data for the matrices `[x, xj+y; Mz, Mzj+pw]`, of determinant one. -/
structure CosetData (p M : ℕ) where
  x : ℤ
  y : ℤ
  z : ℤ
  w : ℤ
  det_eq : (p : ℤ) * x * w - y * M * z = 1

variable {p : ℕ} [hp : Fact p.Prime]

namespace CosetData

/-- The nontrivial coset representatives, for a residue `j`. -/
def gam (D : CosetData p M) (j : ZMod p) : SL(2, ℤ) :=
  ⟨!![D.x, D.x * j.val + D.y; M * D.z, M * D.z * j.val + p * D.w], by
    rw [det_fin_two_of]
    linear_combination D.det_eq⟩

/-- All `p+1` representatives. -/
def rep (D : CosetData p M) : Option (ZMod p) → SL(2, ℤ)
  | none => 1
  | some j => D.gam j

lemma gam_mem (D : CosetData p M) (j : ZMod p) : D.gam j ∈ Gamma0 M := by
  rw [Gamma0_mem]
  simp [gam]

lemma rep_mem (D : CosetData p M) (i : Option (ZMod p)) : D.rep i ∈ Gamma0 M := by
  cases i with
  | none => exact (Gamma0 M).one_mem
  | some j => exact D.gam_mem j

lemma unit_ne_zero (D : CosetData p M) : (((M : ℤ) * D.z : ℤ) : ZMod p) ≠ 0 := by
  intro h
  have he := congrArg (Int.castRingHom (ZMod p)) D.det_eq
  have hz : (M : ZMod p) * (D.z : ZMod p) = 0 := by simpa using h
  simp only [map_sub, map_mul, map_natCast, eq_intCast, map_one, CharP.cast_eq_zero,
    zero_mul, zero_sub] at he
  have : (D.y : ZMod p) * ((M : ZMod p) * D.z) = -1 := by linear_combination -he
  rw [hz, mul_zero] at this
  exact one_ne_zero (neg_eq_zero.mp this.symm)

theorem existsUnique (D : CosetData p M) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    ∃! i, D.rep i * γ ∈ Gamma0 (M * p) :=
  existsUnique_coset rfl D.rep ((M : ℤ) * D.z) rfl D.unit_ne_zero (dvd_mul_right _ _)
    (fun j => by simp [rep, gam]) (fun j => by simp [rep, gam])
    γ hγ

/-- **Mathlib's trace from Γ₀(Mp) to Γ₀(M) as an explicit sum.** -/
theorem trace_eq [NeZero M] (D : CosetData p M) {k : ℤ}
    (f : ModularForm (Gamma0 (M * p) : Subgroup (GL (Fin 2) ℝ)) k)
    [NeZero (M * p)] :
    (ModularForm.trace (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) f : ℍ → ℂ) =
      (f : ℍ → ℂ) + ∑ j : ZMod p, (f : ℍ → ℂ) ∣[k] SpecialLinearGroup.mapGL ℝ (D.gam j) := by
  rw [trace_eq_sum D.rep D.rep_mem D.existsUnique f, Fintype.sum_option]
  simp [rep]

end CosetData

end RamanujanTau.TheoremA.TraceCosets
