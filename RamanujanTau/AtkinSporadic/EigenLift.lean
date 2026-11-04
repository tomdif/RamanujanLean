import RamanujanTau.AtkinSporadic.LiftEquivariance
import RamanujanTau.AtkinSporadic.DimOne
import RamanujanTau.ThetaLift.Final

/-!
# `T(Q²)` is scalar on `η^{−ℓ} S_{ℓ−1}`, from the Shimura lift (characteristic zero)

For `13 ≤ ℓ < 24` and `F = a/η^ℓ`, `a ∈ S_{ℓ−1}(SL₂(ℤ))` integral, every explicit Shimura lift
`S_t F` (`t` squarefree, `t ≡ −ℓ (mod 24)`) is a level-six form of weight `2λ = ℓ − 3`
(`ThetaLift.aadModularity`) in the `U₂, U₃`-eigenspace `W` (`TheoremA.HalfIntegral.U_lift`).
Given `DimOneProp ℓ` (`W` is detected by the coefficient `b(1)`; proved for ℓ = 13, 17, 19, 23 in
`DimOneData`), and since `T_Q` (`TheoremA.GoodHecke.heckeT`) preserves `W`, all lifts are
`T_Q`-eigenforms with one eigenvalue `μ`. The formal equivariance
`S_t(T(Q²)A) = χ₁₂(Q)·T_Q(S_t A)` (`Equivariance.lift_heckeHalf`) and triangularity of the lifts
(`TheoremA.HalfIntegral.chi_coeff_dvd`, `exists_index`) then give, **in characteristic zero**,

  `a(1) · T(Q²)(a·P^ℓ) = χ₁₂(Q) μ · (a·P^ℓ)`        (`eigen_char0`),

and hence `EtaHeckeMod ℓ Q (ℓ−1) ℓ` for every prime `Q ≥ 5` (`etaHeckeMod_of_dimOne`).
-/

set_option autoImplicit false

namespace RamanujanTau.AtkinSporadic.EigenLift
open PowerSeries ModularForm UpperHalfPlane CongruenceSubgroup
open RamanujanTau.TheoremA RamanujanTau.TheoremA.HalfIntegral RamanujanTau.TheoremA.SignLattice
open MockTheta5.JTP (partitionGF)
open DimOne Equivariance
open scoped MatrixGroups ModularForm

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-! ### The eigenspace `W` -/

variable (ℓ) in
/-- Integral level-six forms of weight `2λ` with the lift eigenvalues of `U₂` and `U₃`. -/
def InW (b : PowerSeries ℤ) : Prop :=
  (∃ g : Forms ℓ, PowerSeries.map (Int.castRingHom ℂ) b = qExpansion 1 g) ∧
    BoylanWebb.U 2 b = eig2 ℓ • b ∧ BoylanWebb.U 3 b = eig3 ℓ • b

lemma U_zsmul (p : ℕ) (r : ℤ) (b : PowerSeries ℤ) :
    BoylanWebb.U p (r • b) = r • BoylanWebb.U p b := by
  ext n; rw [BoylanWebb.coeff_U, map_zsmul, map_zsmul, BoylanWebb.coeff_U]

lemma U_sub (p : ℕ) (b c : PowerSeries ℤ) :
    BoylanWebb.U p (b - c) = BoylanWebb.U p b - BoylanWebb.U p c := by
  ext n; simp [BoylanWebb.coeff_U]

lemma InW.comb {b c : PowerSeries ℤ} (hb : InW ℓ b) (hc : InW ℓ c) (x y : ℤ) :
    InW ℓ (x • b - y • c) := by
  obtain ⟨⟨g, hg⟩, hb2, hb3⟩ := hb
  obtain ⟨⟨g', hg'⟩, hc2, hc3⟩ := hc
  refine ⟨⟨(x : ℂ) • g - (y : ℂ) • g', ?_⟩, ?_, ?_⟩
  · have hR : qExpansion 1 (⇑((x : ℂ) • g - (y : ℂ) • g' : Forms ℓ)) =
        (x : ℂ) • qExpansion 1 g - (y : ℂ) • qExpansion 1 g' := by
      change LevelSix.modularExpansionLinear _ ((x : ℂ) • g - (y : ℂ) • g') = _
      rw [map_sub, map_smul, map_smul]
      rfl
    rw [hR, map_sub, map_int_smul, map_int_smul, hg, hg', eq_intCast, eq_intCast]
  · rw [U_sub, U_zsmul, U_zsmul, hb2, hc2, smul_sub, smul_comm x, smul_comm y]
  · rw [U_sub, U_zsmul, U_zsmul, hb3, hc3, smul_sub, smul_comm x, smul_comm y]

lemma eq_zero_of_inW (D : DimOneProp ℓ) {b : PowerSeries ℤ} (hb : InW ℓ b) (h1 : b.coeff 1 = 0) :
    b = 0 := by
  obtain ⟨⟨g, hg⟩, h2, h3⟩ := hb
  exact D b g hg h2 h3 h1

/-! ### `T_Q` on `W` -/

/-- `T_Q` in weight `2λ` on integer q-series. -/
noncomputable def TQ (Q lam : ℕ) (b : PowerSeries ℤ) : PowerSeries ℤ :=
  HeckeQExp.Tq Q ((Q : ℤ) ^ (2 * lam - 1)) b

lemma TQ_comb (Q lam : ℕ) (x y : ℤ) (b c : PowerSeries ℤ) :
    TQ Q lam (x • b - y • c) = x • TQ Q lam b - y • TQ Q lam c := by
  ext n
  simp only [TQ, HeckeQExp.coeff_Tq, map_sub, map_zsmul, smul_eq_mul]
  split_ifs <;> ring

lemma U_TQ {p Q : ℕ} (hQ : Q.Prime) (hpQ : ¬ Q ∣ p) (lam : ℕ) (b : PowerSeries ℤ) :
    BoylanWebb.U p (TQ Q lam b) = TQ Q lam (BoylanWebb.U p b) := by
  have hcop : Nat.Coprime Q p := (Nat.Prime.coprime_iff_not_dvd hQ).mpr hpQ
  ext m
  simp only [TQ, BoylanWebb.coeff_U, HeckeQExp.coeff_Tq]
  rw [Nat.mul_left_comm]
  congr 1
  by_cases hm : Q ∣ m
  · rw [if_pos (hm.mul_left p), if_pos hm, Nat.mul_div_assoc _ hm]
  · rw [if_neg (fun h => hm (hcop.dvd_of_dvd_mul_left h)), if_neg hm]

lemma six_dvd_sq {Q : ℕ} (hQ : Q.Prime) (hQ5 : 5 ≤ Q) : (6 : ℤ) ∣ (Q : ℤ) ^ 2 - 1 := by
  obtain ⟨h2, h3⟩ := prime_ge_five hQ hQ5
  have hs := sq_mod_24 h2 h3
  have h1 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ hQ.pos
  obtain ⟨k, hk⟩ : ∃ k, Q ^ 2 = 24 * k + 1 := ⟨Q ^ 2 / 24, by omega⟩
  refine ⟨4 * k, ?_⟩
  have : ((Q ^ 2 : ℕ) : ℤ) = 24 * k + 1 := by exact_mod_cast hk
  push_cast at this
  linarith

instance neZero_six_mul (Q : ℕ) [hQ : Fact Q.Prime] : NeZero (6 * Q) :=
  ⟨by have := hQ.out.ne_zero; omega⟩

lemma InW.hecke {Q : ℕ} [hQ : Fact Q.Prime] (hQ5 : 5 ≤ Q) (hlam : 1 ≤ halfWt ℓ) {b : PowerSeries ℤ}
    (hb : InW ℓ b) : InW ℓ (TQ Q (halfWt ℓ) b) := by
  obtain ⟨⟨g, hg⟩, hb2, hb3⟩ := hb
  obtain ⟨hQ2, hQ3⟩ := prime_ge_five hQ.out hQ5
  refine ⟨⟨GoodHecke.heckeT (p := Q) (M := 6) g, ?_⟩, ?_, ?_⟩
  · rw [GoodHecke.qExpansion_heckeT (dataGood Q (six_dvd_sq hQ.out hQ5)), ← hg, TQ,
      HeckeQExp.map_Tq]
    congr 1
    have he : (((2 * halfWt ℓ : ℕ) : ℤ) - 1) = ((2 * halfWt ℓ - 1 : ℕ) : ℤ) := by omega
    rw [he, zpow_natCast]
    simp
  · rw [U_TQ hQ.out (fun h => hQ2 ((Nat.prime_dvd_prime_iff_eq hQ.out Nat.prime_two).mp h ▸
      dvd_refl _)), hb2]
    have := TQ_comb Q (halfWt ℓ) (eig2 ℓ) 0 b b
    simpa using this
  · rw [U_TQ hQ.out (fun h => hQ3 ((Nat.prime_dvd_prime_iff_eq hQ.out Nat.prime_three).mp h ▸
      dvd_refl _)), hb3]
    have := TQ_comb Q (halfWt ℓ) (eig3 ℓ) 0 b b
    simpa using this

/-! ### The lifts lie in `W` -/

lemma lift_inW (h13 : 13 ≤ ℓ) {a : PowerSeries ℤ} (ha : a ∈ intLattice ℓ) {t : ℕ}
    (hsf : Squarefree t) (ht : 24 ∣ t + jj ℓ) : InW ℓ (liftSeries ℓ t (coordOf ℓ a)) := by
  obtain ⟨g, hg⟩ := ThetaLift.aadModularity (ℓ := ℓ) (by omega) a ha t hsf ht
  refine ⟨⟨g, hg⟩, ?_, ?_⟩
  · rw [U_lift (Or.inl rfl), psi_two_eq h13 ht]
  · rw [U_lift (Or.inr rfl), psi_three_eq h13 ht]

lemma liftSeries_comb (t : ℕ) (x y : ℤ) (A B : PowerSeries ℤ) :
    liftSeries ℓ t (x • A - y • B) = x • liftSeries ℓ t A - y • liftSeries ℓ t B := by
  ext n
  simp only [coeff_liftSeries, map_sub, map_zsmul, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

lemma zsmul_cancel {α : ℤ} (hα : α ≠ 0) {b c : PowerSeries ℤ} (h : α • b = α • c) : b = c := by
  ext n
  have := congrArg (PowerSeries.coeff n) h
  simp only [map_zsmul, smul_eq_mul] at this
  exact mul_left_cancel₀ hα this

omit hℓ in
lemma coeff_one_coordOf (a : PowerSeries ℤ) (ha0 : a.coeff 0 = 0) :
    (coordOf ℓ a).coeff 1 = a.coeff 1 := by
  have hP : (PowerSeries.map (Int.castRingHom ℤ) partitionGF ^ jj ℓ).coeff 0 = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      MockTheta5.JTP.coeff_partitionGF_eq_card]
    simp
  have hP0 : PowerSeries.constantCoeff partitionGF = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, MockTheta5.JTP.coeff_partitionGF_eq_card]
    simp
  rw [coordOf, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ,
    Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
  simp [ha0, hP0]

omit hℓ in
lemma coeff_zero_coordOf (a : PowerSeries ℤ) (ha0 : a.coeff 0 = 0) : (coordOf ℓ a).coeff 0 = 0 := by
  rw [coordOf, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply a, ha0, zero_mul]

omit hℓ in
lemma coeff_zero_of_intLattice {a : PowerSeries ℤ} (ha : a ∈ intLattice ℓ) : a.coeff 0 = 0 := by
  obtain ⟨G, hG⟩ := ha
  have hc : ModularForm.IsCuspForm (G : ModularForm 𝒮ℒ (kPrime ℓ)) :=
    ⟨G, CuspForm.toModularFormₗ_eq_coe _⟩
  have h := (ModularForm.isCuspForm_iff_coeffZero_eq_zero _).mp hc
  have h2 : (qExpansion 1 G).coeff 0 = 0 := h
  rw [← hG, PowerSeries.coeff_map, eq_intCast] at h2
  exact_mod_cast h2

/-! ### The eigenvalue relation in characteristic zero -/

/-- **`T(Q²)` is scalar on the lift of every form, in characteristic zero.** For `a ∈ S_{ℓ−1}`
integral with `A = a·P^ℓ` and `A(1) ≠ 0`, `A(1)·T(Q²)A = ν·A` for an integer `ν`. -/
theorem eigen_char0 (h13 : 13 ≤ ℓ) (h24 : ℓ < 24) {Q : ℕ} [hQ : Fact Q.Prime] (hQ5 : 5 ≤ Q)
    (D : DimOneProp ℓ) {a : PowerSeries ℤ} (ha : a ∈ intLattice ℓ)
    (hα : (coordOf ℓ a).coeff 1 ≠ 0) :
    ∃ ν : ℤ, (coordOf ℓ a).coeff 1 •
        heckeHalf Q ℓ (halfWt ℓ) (heckeSign Q (halfWt ℓ)) (coordOf ℓ a) = ν • coordOf ℓ a := by
  set A := coordOf ℓ a with hAdef
  set α := A.coeff 1 with hαdef
  have hjj : jj ℓ = ℓ := Nat.mod_eq_of_lt h24
  have hlam : 1 ≤ halfWt ℓ := by unfold halfWt; omega
  -- the reference lift at `t₀ = 24 − ℓ`
  have hprime : ℓ = 13 ∨ ℓ = 17 ∨ ℓ = 19 ∨ ℓ = 23 := by
    have hp := hℓ.out
    interval_cases ℓ <;> first | (left; rfl) | (right; left; rfl) | (right; right; left; rfl) |
      (right; right; right; rfl) | (exfalso; norm_num at hp)
  have hsf0 : Squarefree (24 - ℓ) := by
    rcases hprime with h | h | h | h <;> subst h
    · exact (Nat.Prime.prime (by norm_num : Nat.Prime 11)).squarefree
    · exact (Nat.Prime.prime (by norm_num : Nat.Prime 7)).squarefree
    · exact (Nat.Prime.prime (by norm_num : Nat.Prime 5)).squarefree
    · exact squarefree_one
  have ht0 : 24 ∣ (24 - ℓ) + jj ℓ := by rw [hjj, Nat.sub_add_cancel h24.le]
  set h0 := liftSeries ℓ (24 - ℓ) A with hh0
  have hw0 : InW ℓ h0 := lift_inW h13 ha hsf0 ht0
  have hh01 : h0.coeff 1 = α := by
    rw [hh0, coeff_liftSeries, Nat.divisorsAntidiagonal_one, Finset.sum_singleton]
    have hli : latIndex ℓ (24 - ℓ) 1 = 1 := by
      unfold latIndex; rw [hjj, one_pow, mul_one, Nat.sub_add_cancel h24.le]
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
  set T := heckeHalf (R := ℤ) Q ℓ (halfWt ℓ) (heckeSign Q (halfWt ℓ)) with hTdef
  refine ⟨chi12 Q * μ, ?_⟩
  set Dser := α • T A - (chi12 Q * μ) • A with hD
  have hlift0 : ∀ t, Squarefree t → 24 ∣ t + jj ℓ → liftSeries ℓ t Dser = 0 := by
    intro t hsf ht
    have h := hTL t hsf ht
    simp only [TQ] at h
    rw [hD, liftSeries_comb, hTdef, lift_heckeHalf h13 h24 hQ5 hsf ht, smul_comm α, h,
      mul_smul, sub_self]
  -- triangularity
  have hDc : ∀ m, Dser.coeff m = 0 := by
    intro m
    by_cases hm : m = 0
    · subst hm
      have hA0 : A.coeff 0 = 0 := coeff_zero_coordOf a (coeff_zero_of_intLattice ha)
      have hT0' : (T A).coeff 0 = 0 := by
        rw [hTdef, coeff_heckeHalf, hA0]
        have h1 : ¬ hshift Q ℓ ≤ Q ^ 2 * 0 := by
          obtain ⟨hQ2, hQ3⟩ := prime_ge_five hQ.out hQ5
          have hd := hshift_spec hQ2 hQ3 ℓ
          have : 24 ≤ Q ^ 2 := by nlinarith
          intro hle
          rw [mul_zero, Nat.le_zero] at hle
          rw [hle] at hd
          have : 1 ≤ (Q ^ 2 - 1) * ℓ := Nat.one_le_iff_ne_zero.mpr
            (mul_ne_zero (by omega) (by omega))
          omega
        have h2 : ¬ Q ^ 2 ∣ 0 + hshift Q ℓ := by
          rintro ⟨k, hk⟩
          obtain ⟨hQ2, hQ3⟩ := prime_ge_five hQ.out hQ5
          have hd := hshift_spec hQ2 hQ3 ℓ
          rw [zero_add] at hk
          rw [hk] at hd
          have hQ1 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ hQ.out.pos
          have : Q ^ 2 ∣ ℓ := by
            have e : ℓ = Q ^ 2 * ℓ - Q ^ 2 * (24 * k) := by
              rw [Nat.sub_mul, one_mul] at hd
              have : Q ^ 2 * (24 * k) = 24 * (Q ^ 2 * k) := by ring
              omega
            rw [e, ← Nat.mul_sub]
            exact dvd_mul_right _ _
          rcases (Nat.dvd_prime hℓ.out).mp this with h | h
          · have : Q ≤ 1 := by nlinarith
            omega
          · have hQl : Q ∣ ℓ := (dvd_pow_self Q two_ne_zero).trans (h ▸ dvd_refl _)
            have := (Nat.prime_dvd_prime_iff_eq hQ.out hℓ.out).mp hQl
            subst this
            nlinarith [hQ.out.two_le]
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

end RamanujanTau.AtkinSporadic.EigenLift
