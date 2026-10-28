import RamanujanTau.DBound.Limit

/-!
# Square roots in `B_E(r)` (coordinates)

**`sqrt_Ap`**: let `B` be subadditive along Katz products (`B m ≤ B k + B l` for `m ≤ k + l`) with
`B 0 = 0`. If `w ≡ 1 (mod ℓ)` as a q-series and `w²` has approximate Katz expansions with `v_i ≥ B i`,
then so does `w`.

This replaces the binomial series `(1+h)^{1/2} = Σ C(1/2,n) hⁿ` by the equivalent Newton/Hensel
iteration `w ≡ P_N (mod ℓ^{N+1})`, `P_{N+1} = P_N + (H − P_N²)/2` with `H ≡ w² (mod ℓ^{N+2})`
(`ℓ` odd, so `2 ∈ ℤ_ℓ^×`), in which every step keeps the bound `B` exactly.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace DBound
open MvPolynomial ModP AtkinOBrienFinal AtkinOBrien PowerSeries

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] {hℓ : 5 ≤ ℓ}

variable (hℓ) in
/-- `F` is a finite Katz series with `v_i ≥ B i`. -/
def KS (B : ℕ → ℕ) (F : PS ℓ) : Prop :=
  ∃ I, ∃ a : ℕ → Poly ℓ, (∀ i, a i ∈ Kpiece ℓ hℓ i) ∧ (∀ i, Dvd (ℓ : ℤ_[ℓ]) (B i) (a i)) ∧
    F = ksum (hℓ := hℓ) I a

lemma ksum_trunc {I J : ℕ} (a : ℕ → Poly ℓ) (h : I ≤ J) :
    ksum (hℓ := hℓ) J (trunc I a) = ksum (hℓ := hℓ) I a := by
  rw [ksum, ← Finset.sum_range_add_sum_Ico _ h]
  rw [Finset.sum_eq_zero (s := Finset.Ico I J) (fun i hi => by
    rw [AtkinOBrienFinal.trunc, if_neg (by simp at hi; omega), map_zero, zero_mul]), add_zero]
  exact Finset.sum_congr rfl fun i hi => by
    rw [AtkinOBrienFinal.trunc, if_pos (Finset.mem_range.mp hi)]

lemma KS_add {B : ℕ → ℕ} {F G : PS ℓ} (hF : KS hℓ B F) (hG : KS hℓ B G) : KS hℓ B (F + G) := by
  obtain ⟨I, a, haK, haB, rfl⟩ := hF
  obtain ⟨J, b, hbK, hbB, rfl⟩ := hG
  refine ⟨max I J, trunc I a + trunc J b, fun i => Submodule.add_mem _ (trunc_mem hℓ haK i)
    (trunc_mem hℓ hbK i), fun i => Dvd_add (trunc_dvd i (haB i)) (trunc_dvd i (hbB i)), ?_⟩
  rw [← ksum_trunc a (le_max_left I J), ← ksum_trunc b (le_max_right I J)]
  simp only [ksum, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

lemma KS_smul {B : ℕ → ℕ} (r : ℤ_[ℓ]) {F : PS ℓ} (hF : KS hℓ B F) : KS hℓ B (r • F) := by
  obtain ⟨I, a, haK, haB, rfl⟩ := hF
  exact ⟨I, fun i => r • a i, fun i => Submodule.smul_mem _ r (haK i), fun i => Dvd_smul r (haB i),
    (ksum_smul I r a).symm⟩

lemma KS_sub {B : ℕ → ℕ} {F G : PS ℓ} (hF : KS hℓ B F) (hG : KS hℓ B G) : KS hℓ B (F - G) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℤ_[ℓ] G]
  exact KS_add hF (KS_smul _ hG)

lemma KS_one {B : ℕ → ℕ} (h0 : B 0 = 0) : KS hℓ B (1 : PS ℓ) := by
  classical
  refine ⟨1, fun i => if i = 0 then 1 else 0, fun i => ?_, fun i => ?_, ?_⟩
  · dsimp only; split_ifs with h
    · subst h; exact one_mem_Kpiece
    · exact Submodule.zero_mem _
  · dsimp only; split_ifs with h
    · subst h; rw [h0]; exact ⟨1, by simp⟩
    · exact Dvd_zero _
  · simp [ksum]

lemma KS_of_KA {B : ℕ → ℕ} {N : ℕ} {f : PS ℓ} (h : KA hℓ B N f) :
    ∃ F, KS hℓ B F ∧ Dvd (ℓ : ℤ_[ℓ]) N (f - F) := by
  obtain ⟨I, a, haK, haA, haB⟩ := h
  exact ⟨ksum (hℓ := hℓ) I a, ⟨I, a, haK, haB, rfl⟩, haA⟩

lemma KA_of_KS {B : ℕ → ℕ} {N : ℕ} {f F : PS ℓ} (hF : KS hℓ B F) (h : Dvd (ℓ : ℤ_[ℓ]) N (f - F)) :
    KA hℓ B N f := by
  obtain ⟨I, a, haK, haB, rfl⟩ := hF
  exact ⟨I, a, haK, h, haB⟩

lemma KS_mul {B : ℕ → ℕ} (hB : ∀ k l m, m ≤ k + l → B m ≤ B k + B l) {F G : PS ℓ}
    (hF : KS hℓ B F) (hG : KS hℓ B G) (N : ℕ) : ∃ H, KS hℓ B H ∧ Dvd (ℓ : ℤ_[ℓ]) N (F * G - H) := by
  obtain ⟨I, a, haK, haB, rfl⟩ := hF
  obtain ⟨J, b, hbK, hbB, rfl⟩ := hG
  obtain ⟨c, hcK, hcB, hcD⟩ := fin_mul B B B hB N I J a b haK hbK haB hbB
  exact ⟨_, ⟨I + J, c, hcK, hcB, rfl⟩, hcD⟩

lemma isUnit_two (h5 : 5 ≤ ℓ) : IsUnit (2 : ℤ_[ℓ]) := by
  have h2 : ℓ ≠ 2 := by omega
  rw [PadicInt.isUnit_iff, show (2 : ℤ_[ℓ]) = ((2 : ℕ) : ℤ_[ℓ]) by norm_num,
    PadicInt.norm_natCast_eq_one_iff]
  exact (Nat.coprime_primes hℓp.out Nat.prime_two).mpr h2

/-- **Square roots.** -/
theorem sqrt_Ap {B : ℕ → ℕ} (hB : ∀ k l m, m ≤ k + l → B m ≤ B k + B l) (hB0 : B 0 = 0) {w : PS ℓ}
    (hw1 : Dvd (ℓ : ℤ_[ℓ]) 1 (w - 1)) (hw2 : Ap hℓ B (w * w)) : Ap hℓ B w := by
  obtain ⟨u, hu⟩ := isUnit_two (ℓ := ℓ) hℓ
  set i2 : ℤ_[ℓ] := ↑u⁻¹ with hi2
  have hi2' : i2 * 2 = 1 := by rw [hi2, ← hu, Units.inv_mul]
  obtain ⟨z, hz⟩ := hw1
  -- `w ≡ P_N (mod ℓ^{N+1})`
  have key : ∀ N, ∃ P, KS hℓ B P ∧ Dvd (ℓ : ℤ_[ℓ]) (N + 1) (w - P) := by
    intro N
    induction N with
    | zero => exact ⟨1, KS_one hB0, ⟨z, hz⟩⟩
    | succ N ih =>
      obtain ⟨P, hP, e, he⟩ := ih
      obtain ⟨H, hH, hHd⟩ := KS_of_KA (hw2 (N + 2))
      obtain ⟨H', hH', hH'd⟩ := KS_mul hB hP hP (N + 2)
      refine ⟨P + i2 • (H - H'), KS_add hP (KS_smul _ (KS_sub hH hH')), ?_⟩
      obtain ⟨t, ht⟩ := hHd
      obtain ⟨t', ht'⟩ := hH'd
      -- `w + P = 2 + ℓ y`
      have hwP : w + P - 2 = (ℓ : ℤ_[ℓ]) • (2 * z - (ℓ : ℤ_[ℓ]) ^ N • e) := by
        have : P = w - (ℓ : ℤ_[ℓ]) ^ (N + 1) • e := by rw [← he]; abel
        rw [this]
        have hz' := hz
        rw [pow_one] at hz'
        simp only [Algebra.smul_def, map_pow] at hz' ⊢
        linear_combination 2 * hz'
      set y := 2 * z - (ℓ : ℤ_[ℓ]) ^ N • e
      refine ⟨i2 • (t - t' - e * y), ?_⟩
      have hw : w = P + (ℓ : ℤ_[ℓ]) ^ (N + 1) • e := by rw [← he]; abel
      have hH2 : H = w * w - (ℓ : ℤ_[ℓ]) ^ (N + 2) • t := by rw [← ht]; abel
      have hH'2 : H' = P * P - (ℓ : ℤ_[ℓ]) ^ (N + 2) • t' := by rw [← ht']; abel
      have hy : w + P = 2 + (ℓ : ℤ_[ℓ]) • y := by rw [← hwP]; abel
      have hww : w * w - P * P = ((ℓ : ℤ_[ℓ]) ^ (N + 1) • e) * (2 + (ℓ : ℤ_[ℓ]) • y) := by
        rw [← hy, ← he]; ring
      have hc : (algebraMap ℤ_[ℓ] (PS ℓ)) i2 * 2 = 1 := by
        rw [show (2 : PS ℓ) = algebraMap ℤ_[ℓ] (PS ℓ) 2 from (map_ofNat _ 2).symm, ← map_mul, hi2',
          map_one]
      rw [hH2, hH'2]
      simp only [Algebra.smul_def, map_pow] at hw hww ⊢
      linear_combination hw - (algebraMap ℤ_[ℓ] (PS ℓ) i2) * hww -
        (algebraMap ℤ_[ℓ] (PS ℓ) ℓ) ^ (N + 1) * e * hc
  intro N
  obtain ⟨P, hP, hd⟩ := key N
  exact KA_of_KS hP (Dvd_mono (Nat.le_succ N) hd)

end DBound
