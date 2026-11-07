import RamanujanTau.AtkinSporadic.EigenLift
import RamanujanTau.OnoWeaverMore.LiftEquivJ

/-!
# `T(Q²)` is scalar on `η^{−j} S_{k'}`, for every prime `ℓ ≥ 13` with a dimension-one certificate

`AtkinSporadic.EigenLift.eigen_char0` for `13 ≤ ℓ < 24`, extended to all `ℓ ≥ 13`: the operator
is `T(Q²)` in the coordinate `coordOf ℓ` (`η^{−j}`, `j = ℓ mod 24`), the reference lift is at
`t₀ = 24 − j` (assumed squarefree: `t₀ = 19` at ℓ = 29, `t₀ = 17` at ℓ = 31), and the formal
equivariance is `EquivarianceJ.lift_heckeHalfJ`. Same proof otherwise: all lifts lie in the
`U₂, U₃`-eigenspace `W` of `M_{ℓ−3}(Γ₀(6))`, `DimOneProp ℓ` makes `T_Q` scalar on them, and
triangularity of the lifts gives, in characteristic zero,

  `a(1) · T(Q²)(coordOf ℓ a) = ν · coordOf ℓ a`        (`eigen_char0J`).
-/

set_option autoImplicit false

namespace RamanujanTau.OnoWeaverMore.EigenLiftJ
open PowerSeries ModularForm UpperHalfPlane CongruenceSubgroup
open RamanujanTau.TheoremA RamanujanTau.TheoremA.HalfIntegral RamanujanTau.TheoremA.SignLattice
open RamanujanTau.AtkinSporadic RamanujanTau.AtkinSporadic.EigenLift
open MockTheta5.JTP (partitionGF)
open DimOne Equivariance
open scoped MatrixGroups ModularForm

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- **`T(Q²)` is scalar on the lift of every form, in characteristic zero.** For `a ∈ S_{ℓ−1}`
integral with `A = a·P^ℓ` and `A(1) ≠ 0`, `A(1)·T(Q²)A = ν·A` for an integer `ν`. -/
theorem eigen_char0J (h13 : 13 ≤ ℓ) (hsf0 : Squarefree (24 - jj ℓ)) {Q : ℕ} [hQ : Fact Q.Prime]
    (hQ5 : 5 ≤ Q) (D : DimOneProp ℓ) {a : PowerSeries ℤ} (ha : a ∈ intLattice ℓ)
    (hα : (coordOf ℓ a).coeff 1 ≠ 0) :
    ∃ ν : ℤ, (coordOf ℓ a).coeff 1 •
        heckeHalf Q (jj ℓ) (halfWt ℓ) (heckeSign Q (halfWt ℓ)) (coordOf ℓ a) = ν • coordOf ℓ a := by
  set A := coordOf ℓ a with hAdef
  set α := A.coeff 1 with hαdef
  have hj24 : jj ℓ < 24 := Nat.mod_lt _ (by norm_num)
  have hlam : 1 ≤ halfWt ℓ := by unfold halfWt; omega
  have ht0 : 24 ∣ (24 - jj ℓ) + jj ℓ := by rw [Nat.sub_add_cancel hj24.le]
  set h0 := liftSeries ℓ (24 - jj ℓ) A with hh0
  have hw0 : InW ℓ h0 := lift_inW h13 ha hsf0 ht0
  have hh01 : h0.coeff 1 = α := by
    rw [hh0, coeff_liftSeries, Nat.divisorsAntidiagonal_one, Finset.sum_singleton]
    have hli : latIndex ℓ (24 - jj ℓ) 1 = 1 := by
      unfold latIndex; rw [one_pow, mul_one, Nat.sub_add_cancel hj24.le]
    simp [psi, chi12, hli, hαdef]
  set μ := (TQ Q (halfWt ℓ) h0).coeff 1 with hμ
  have hT0 : α • TQ Q (halfWt ℓ) h0 = μ • h0 := by
    have h := eq_zero_of_inW D ((hw0.hecke hQ5 hlam).comb hw0 α μ) (by
      simp only [map_sub, map_zsmul, smul_eq_mul, hh01, ← hμ]; ring)
    exact sub_eq_zero.mp h
  -- every lift is a `T_Q`-eigenform with eigenvalue `μ/α`
  have hTL : ∀ t, Squarefree t → 24 ∣ t + jj ℓ →
      α • TQ Q (halfWt ℓ) (liftSeries ℓ t A) = μ • liftSeries ℓ t A := by
    intro t hsf ht
    set L := liftSeries ℓ t A
    have hwL : InW ℓ L := lift_inW h13 ha hsf ht
    have hL1 : α • L = L.coeff 1 • h0 := by
      have h := eq_zero_of_inW D (hwL.comb hw0 α (L.coeff 1)) (by
        simp only [map_sub, map_zsmul, smul_eq_mul, hh01]; ring)
      exact sub_eq_zero.mp h
    have hs : ∀ (x : ℤ) (b : PowerSeries ℤ), TQ Q (halfWt ℓ) (x • b) = x • TQ Q (halfWt ℓ) b := by
      intro x b
      simpa using TQ_comb Q (halfWt ℓ) x 0 b b
    apply zsmul_cancel hα
    calc α • (α • TQ Q (halfWt ℓ) L) = α • TQ Q (halfWt ℓ) (α • L) := by rw [hs]
      _ = α • TQ Q (halfWt ℓ) (L.coeff 1 • h0) := by rw [hL1]
      _ = L.coeff 1 • (α • TQ Q (halfWt ℓ) h0) := by rw [hs, smul_comm]
      _ = L.coeff 1 • (μ • h0) := by rw [hT0]
      _ = μ • (α • L) := by rw [hL1, smul_comm]
      _ = α • (μ • L) := smul_comm _ _ _
  -- the defect has vanishing lifts
  set T := heckeHalf (R := ℤ) Q (jj ℓ) (halfWt ℓ) (heckeSign Q (halfWt ℓ)) with hTdef
  refine ⟨chi12 Q * μ, ?_⟩
  set Dser := α • T A - (chi12 Q * μ) • A with hD
  have hlift0 : ∀ t, Squarefree t → 24 ∣ t + jj ℓ → liftSeries ℓ t Dser = 0 := by
    intro t hsf ht
    have h := hTL t hsf ht
    simp only [TQ] at h
    rw [hD, liftSeries_comb, hTdef, EquivarianceJ.lift_heckeHalfJ h13 hQ5 hsf ht, smul_comm α, h,
      mul_smul, sub_self]
  -- triangularity
  have hDc : ∀ m, Dser.coeff m = 0 := by
    intro m
    by_cases hm : m = 0
    · subst hm
      have hA0 : A.coeff 0 = 0 := coeff_zero_coordOf a (coeff_zero_of_intLattice ha)
      have hT0' : (T A).coeff 0 = 0 := by
        rw [hTdef, coeff_heckeHalf, hA0]
        obtain ⟨hQ2, hQ3⟩ := prime_ge_five hQ.out hQ5
        have hd := hshift_spec hQ2 hQ3 (jj ℓ)
        have hQ25 : 25 ≤ Q ^ 2 := by nlinarith
        have hjodd : jj ℓ % 2 = 1 := by
          have := (prime_ge h13).1
          unfold jj; omega
        have h1 : ¬ hshift Q (jj ℓ) ≤ Q ^ 2 * 0 := by
          intro hle
          rw [mul_zero, Nat.le_zero] at hle
          rw [hle] at hd
          have : 1 ≤ (Q ^ 2 - 1) * jj ℓ := Nat.one_le_iff_ne_zero.mpr
            (mul_ne_zero (by omega) (by omega))
          omega
        have h2 : ¬ Q ^ 2 ∣ 0 + hshift Q (jj ℓ) := by
          rintro ⟨k, hk⟩
          rw [zero_add] at hk
          rw [hk] at hd
          -- `jj ℓ = Q² (jj ℓ − 24 k)`, impossible for `0 < jj ℓ < 24 < Q²`
          have e : Q ^ 2 * jj ℓ = jj ℓ + Q ^ 2 * (24 * k) := by
            rw [Nat.sub_mul, one_mul] at hd
            have h3 : jj ℓ ≤ Q ^ 2 * jj ℓ := Nat.le_mul_of_pos_left _ (by omega)
            have : 24 * (Q ^ 2 * k) = Q ^ 2 * (24 * k) := by ring
            omega
          have hlt : 24 * k < jj ℓ := by
            by_contra hge
            push Not at hge
            have : Q ^ 2 * jj ℓ ≤ Q ^ 2 * (24 * k) := Nat.mul_le_mul_left _ hge
            omega
          have : Q ^ 2 * (jj ℓ - 24 * k) = jj ℓ := by rw [Nat.mul_sub]; omega
          have h4 : 1 ≤ jj ℓ - 24 * k := by omega
          have : Q ^ 2 ≤ jj ℓ := by
            calc Q ^ 2 = Q ^ 2 * 1 := by ring
              _ ≤ Q ^ 2 * (jj ℓ - 24 * k) := Nat.mul_le_mul_left _ h4
              _ = jj ℓ := this
          omega
        rw [if_neg h1, if_neg h2]
        simp
      rw [hD, map_sub, map_zsmul, map_zsmul, hT0', hA0]
      simp
    obtain ⟨t, e, hsf, ht, he2, he3, he0, hidx⟩ := exists_index (ℓ := ℓ) h13 hm
    have hd := chi_coeff_dvd (ℓ := ℓ) (t := t) Dser 0 (fun n => by
      rw [hlift0 t hsf ht, map_zero]) e he0
    rw [zero_dvd_iff, hidx] at hd
    rcases chi12_ne_zero he2 he3 with h | h
    · rwa [h, one_mul] at hd
    · rwa [h, neg_one_mul, neg_eq_zero] at hd
  have hD0 : Dser = 0 := by
    ext m
    rw [hDc m, map_zero]
  exact sub_eq_zero.mp hD0

end RamanujanTau.OnoWeaverMore.EigenLiftJ
