import RamanujanTau.FiniteArithmetic.SmallThreshold

/-!
# Boylan–Webb's threshold `b_ℓ(4) = b_ℓ(5) = 5` at 13, 17, 19, 23

For `ℓ ∈ {13, 17, 19, 23}` and `m ≥ 4`, `b_ℓ(m) ≥ 5`: no scalar `c` satisfies
`ℓ⁴ ∣ L(5) - c L(3)`. This is certified by a 2-by-2 determinant of partition numbers modulo
`ℓ⁴`, `p(ℓ³ - e₃) p(2ℓ⁵ - e₅) - p(2ℓ³ - e₃) p(ℓ⁵ - e₅) ≢ 0`, read from a kernel-certified prefix of
the partition numbers modulo `ℓ⁴` (`PartitionPrefix.pgfPrefixG`; up to 6,704,525 terms at 23).
With `SmallThreshold` this gives `b_ℓ(4) = b_ℓ(5) = 5`.
-/
set_option autoImplicit false

namespace RamanujanTau.FiniteArithmetic.SmallThresholdFive

open PowerSeries AtkinOBrien BoylanWebb AtkinOBrienFinal Packed SmallThreshold
open MockTheta5.JTP (partitionGF)

/-- The determinant certificate on a long prefix. -/
def detOkG (Q R N d k n ku kb kc i1 i2 j1 j2 : ℕ) : Bool :=
  match PartitionPrefix.pgfPrefixG Q R N d k n ku kb kc with
  | some B => (lane B i1 * lane B j2) % Q != (lane B i2 * lane B j1) % Q
  | none => false

section
variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

/-- **No scalar recurrence from `b` modulo `ℓ^e`**, from a determinant certificate. -/
theorem fail_of_detOkG (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) (b e R N d k n ku kb kc kN i1 i2 j1 j2 : ℕ)
    (hQ : ℓ ^ e ≤ 2 ^ 21) (hk : ku + kb + kN < 64) (hno : 2 ^ 22 + ℓ ^ e * 2 ^ kc ≤ x)
    (hN0 : 0 < N) (hN : N ≤ 2 ^ kN) (hn : k * 2 ^ d ≤ 2 ^ 20)
    (hJ : N ≤ PartitionPrefix.pentLow (k * 2 ^ d))
    (hi1 : (ℓ : ℤ) ^ b * (1 : ℕ) - eB ℓ b = i1) (hi2 : (ℓ : ℤ) ^ b * (2 : ℕ) - eB ℓ b = i2)
    (hj1 : (ℓ : ℤ) ^ (b + 2) * (1 : ℕ) - eB ℓ (b + 2) = j1)
    (hj2 : (ℓ : ℤ) ^ (b + 2) * (2 : ℕ) - eB ℓ (b + 2) = j2)
    (hlt : i1 < N ∧ i2 < N ∧ j1 < N ∧ j2 < N)
    (hok : detOkG (ℓ ^ e) R N d k n ku kb kc i1 i2 j1 j2 = true) (c : ℤ_[ℓ]) :
    ¬ Dvd (ℓ : ℤ_[ℓ]) e (Ll ℓ (b + 2) - c • Ll ℓ b) := by
  intro hc
  unfold detOkG at hok
  cases hB : PartitionPrefix.pgfPrefixG (ℓ ^ e) R N d k n ku kb kc with
  | none => rw [hB] at hok; exact absurd hok (by simp)
  | some B =>
    rw [hB] at hok
    have hne : (lane B i1 * lane B j2) % (ℓ ^ e) ≠ (lane B i2 * lane B j1) % (ℓ ^ e) := by
      simpa using hok
    have hQ1 : 1 ≤ ℓ ^ e := Nat.one_le_pow _ _ hℓp.out.pos
    have hcoeff := PartitionPrefix.coeff_pgfG hQ1 hQ hk hno hN0 hN hn hJ hB
    have hrel : ∀ (m : ℕ) (a a' : ℕ), (ℓ : ℤ) ^ (b + 2) * m - eB ℓ (b + 2) = a →
        (ℓ : ℤ) ^ b * m - eB ℓ b = a' → a < N → a' < N →
        (lane B a : ZMod (ℓ ^ e)) = PadicInt.toZModPow e c * (lane B a' : ZMod (ℓ ^ e)) := by
      intro m a a' ha ha' haN ha'N
      obtain ⟨y, hy⟩ := pser_dvd_gen h24 c b e hc m
      have h := congrArg (PadicInt.toZModPow (p := ℓ) e) hy
      rw [ha, ha', pZ_nat, pZ_nat, map_sub, map_mul, map_mul, map_intCast, map_intCast, map_pow,
        map_natCast, ← Nat.cast_pow, ZMod.natCast_self, zero_mul, sub_eq_zero] at h
      rw [← hcoeff a haN, ← hcoeff a' ha'N]
      exact h
    have e1 := hrel 1 j1 i1 hj1 hi1 hlt.2.2.1 hlt.1
    have e2 := hrel 2 j2 i2 hj2 hi2 hlt.2.2.2 hlt.2.1
    apply hne
    rw [← ZMod.natCast_eq_natCast_iff']
    push_cast
    rw [e1, e2]
    ring

/-- Unit coefficient of `L(b)` from the rank-one reduction. -/
theorem unit_coeff_b (b : ℕ) (f : PowerSeries ℤ) (y : ZMod ℓ) (hy : y ≠ 0)
    (hL : Ψ ℓ (L ℓ b) = C y * Ψ ℓ f) (hf : coeff 1 (Ψ ℓ f) ≠ 0) :
    PadicInt.toZMod (coeff 1 (Ll ℓ b)) ≠ 0 := by
  have h : PadicInt.toZMod (coeff 1 (Ll ℓ b)) = coeff 1 (Ψ ℓ (L ℓ b)) := by
    rw [Ll, coeff_map, Ψ, coeff_map]
    simp
  rw [h, hL, coeff_C_mul]
  exact mul_ne_zero hy hf

/-- Every later odd iterate is a power of `κ` times `L(2k+3)`, modulo `ℓ^e` for `e ≤ 2k+3`. -/
theorem later (κ : ℤ_[ℓ]) (hser : ∀ b, 1 ≤ b → Dvd (ℓ : ℤ_[ℓ]) b (Ll ℓ (b + 2) - κ • Ll ℓ b))
    (k e : ℕ) (he : e ≤ 2 * k + 3) (j : ℕ) :
    Dvd (ℓ : ℤ_[ℓ]) e (Ll ℓ (2 * (k + 1 + j) + 1) - κ ^ j • Ll ℓ (2 * (k + 1) + 1)) := by
  induction j with
  | zero => exact ⟨0, by simp⟩
  | succ j ih =>
    have hs := hser (2 * (k + 1 + j) + 1) (by omega)
    have he' : Ll ℓ (2 * (k + 1 + (j + 1)) + 1) - κ ^ (j + 1) • Ll ℓ (2 * (k + 1) + 1) =
        (Ll ℓ (2 * (k + 1 + j) + 1 + 2) - κ • Ll ℓ (2 * (k + 1 + j) + 1)) +
          κ • (Ll ℓ (2 * (k + 1 + j) + 1) - κ ^ j • Ll ℓ (2 * (k + 1) + 1)) := by
      rw [show 2 * (k + 1 + (j + 1)) + 1 = 2 * (k + 1 + j) + 1 + 2 by ring, smul_sub, smul_smul,
        pow_succ']
      abel
    rw [he']
    exact Dvd_add (Dvd_mono (by omega) hs) (Dvd_smul _ ih)

/-- **Assembly**: `b_ℓ(m) ≥ 5` for `m ≥ 4`. -/
theorem five_le (h13 : 13 ≤ ℓ) (κ : ℤ_[ℓ]) (hκ : PadicInt.toZMod κ ≠ 0)
    (hser : ∀ b, 1 ≤ b → Dvd (ℓ : ℤ_[ℓ]) b (Ll ℓ (b + 2) - κ • Ll ℓ b))
    (hunit : PadicInt.toZMod (coeff 1 (Ll ℓ (2 * 1 + 1))) ≠ 0)
    (hfail : ∀ c : ℤ_[ℓ], ¬ Dvd (ℓ : ℤ_[ℓ]) 4 (Ll ℓ 5 - c • Ll ℓ 3))
    (h3 : ∀ m, 2 ≤ m → 3 ≤ BLBound.bEll ℓ m) (m : ℕ) (hm : 4 ≤ m) :
    5 ≤ BLBound.bEll ℓ m := by
  have hnot := BLBound.not_mem_of_scalar κ 1 4 m hm (later κ hser 1 4 (by omega))
    (Dvd_mono (by norm_num) (hser 3 (by omega))) 1 hunit (fun c => by simpa using hfail c)
  have hn3 : 3 ∉ BLBound.bSet ℓ m := BLBound.not_mem_bSet h13 m (by omega) 1 (by simpa using hnot)
  have hodd : ∀ j, Dvd (ℓ : ℤ_[ℓ]) (2 * j + 1)
      (Ll ℓ (2 * j + 3) - κ • Ll ℓ (2 * j + 1)) := fun j => hser (2 * j + 1) (by omega)
  have hne : (BLBound.bSet ℓ m).Nonempty :=
    ⟨_, BLBound.mem_bSet_of_scalar m (m / 2) κ hκ fun j hj => Dvd_mono (by omega) (hodd j)⟩
  have hmem := Nat.sInf_mem hne
  have hge := h3 m (by omega)
  unfold BLBound.bEll at hge ⊢
  obtain ⟨⟨r, hr⟩, -⟩ := hmem
  by_contra hlt
  have : sInf (BLBound.bSet ℓ m) = 3 := by omega
  exact hn3 (this ▸ Nat.sInf_mem hne)

end

/-! ### The four primes -/

theorem cert13 : detOkG (13 ^ 4) 257049 541470 8 3 20 15 21 47 1007 3204 170176 541469 = true := by
  decide +kernel
theorem cert17 :
    detOkG (17 ^ 4) 250563 1833983 8 5 21 17 21 46 1433 6346 414125 1833982 = true := by
  decide +kernel
theorem cert19 :
    detOkG (19 ^ 4) 260642 2991954 8 6 22 17 21 46 1429 8288 515854 2991953 = true := by
  decide +kernel
theorem cert23 :
    detOkG (23 ^ 4) 279841 6704525 8 9 23 19 21 45 507 12674 268181 6704524 = true := by
  decide +kernel

/-- Assembly at one prime from its inputs. -/
theorem five_of {ℓ : ℕ} [Fact ℓ.Prime] (h13 : 13 ≤ ℓ) (κ : ℤ_[ℓ]) (hκ : PadicInt.toZMod κ ≠ 0)
    (hser : ∀ b, 1 ≤ b → Dvd (ℓ : ℤ_[ℓ]) b (Ll ℓ (b + 2) - κ • Ll ℓ b))
    (hunit : PadicInt.toZMod (coeff 1 (Ll ℓ (2 * 1 + 1))) ≠ 0)
    (hfail : ∀ c : ℤ_[ℓ], ¬ Dvd (ℓ : ℤ_[ℓ]) 4 (Ll ℓ 5 - c • Ll ℓ 3))
    (hsmall : ∀ m, 1 ≤ m → (2 ≤ m → 3 ≤ BLBound.bEll ℓ m) ∧ BLBound.bEll ℓ m ≤ 2 * (m / 2) + 1) :
    BLBound.bEll ℓ 4 = 5 ∧ BLBound.bEll ℓ 5 = 5 ∧ ∀ m, 4 ≤ m → 5 ≤ BLBound.bEll ℓ m := by
  have h5 := five_le h13 κ hκ hser hunit hfail (fun m hm => (hsmall m (by omega)).1 hm)
  have u4 := (hsmall 4 (by norm_num)).2
  have u5 := (hsmall 5 (by norm_num)).2
  have l4 := h5 4 le_rfl
  have l5 := h5 5 (by norm_num)
  norm_num at u4 u5
  exact ⟨by omega, by omega, h5⟩

/-- **`b₁₃(4) = b₁₃(5) = 5`.** -/
theorem bEll_13 : BLBound.bEll 13 4 = 5 ∧ BLBound.bEll 13 5 = 5 ∧
    ∀ m, 4 ≤ m → 5 ≤ BLBound.bEll 13 m := by
  obtain ⟨hUB, hDB⟩ := ub_db (ℓ := 13) (by norm_num) (by norm_num)
  obtain ⟨κ, hκ, hser⟩ := L_padic (ℓ := 13) (by norm_num) le_rfl (by norm_num) Cert13.h24 6
    Cert13.f Cert13.form_f Cert13.coeff_zero_f coeff_one_13 Cert13.rank_one Cert13.two_step hUB hDB
  obtain ⟨y, hy, hL⟩ := Cert13.rank_one 3 (by norm_num)
  exact five_of (by norm_num) κ (by rw [toZMod_kappa κ 6 hκ]; decide) hser
    (unit_coeff_b 3 _ y hy hL coeff_one_13)
    (fail_of_detOkG Cert13.h24 3 4 257049 541470 8 3 20 15 21 47 20 1007 3204 170176 541469
      (by norm_num) (by norm_num) (by norm_num [x]) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [PartitionPrefix.pentLow])
      (by norm_num [eB, ek]) (by norm_num [eB, ek]) (by norm_num [eB, ek]) (by norm_num [eB, ek])
      (by norm_num) cert13)
    SmallThreshold.bEll_13.2.2.2

/-- **`b₁₇(4) = b₁₇(5) = 5`.** -/
theorem bEll_17 : BLBound.bEll 17 4 = 5 ∧ BLBound.bEll 17 5 = 5 ∧
    ∀ m, 4 ≤ m → 5 ≤ BLBound.bEll 17 m := by
  obtain ⟨hUB, hDB⟩ := ub_db (ℓ := 17) (by norm_num) (by norm_num)
  obtain ⟨κ, hκ, hser⟩ := L_padic (ℓ := 17) (by norm_num) (by norm_num) (by norm_num) Cert17.h24 6
    Cert17.f Cert17.form_f Cert17.coeff_zero_f coeff_one_17 Cert17.rank_one Cert17.two_step hUB hDB
  obtain ⟨y, hy, hL⟩ := Cert17.rank_one 3 (by norm_num)
  exact five_of (by norm_num) κ (by rw [toZMod_kappa κ 6 hκ]; decide) hser
    (unit_coeff_b 3 _ y hy hL coeff_one_17)
    (fail_of_detOkG Cert17.h24 3 4 250563 1833983 8 5 21 17 21 46 21 1433 6346 414125 1833982
      (by norm_num) (by norm_num) (by norm_num [x]) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [PartitionPrefix.pentLow])
      (by norm_num [eB, ek]) (by norm_num [eB, ek]) (by norm_num [eB, ek]) (by norm_num [eB, ek])
      (by norm_num) cert17)
    SmallThreshold.bEll_17.2.2.2

/-- **`b₁₉(4) = b₁₉(5) = 5`.** -/
theorem bEll_19 : BLBound.bEll 19 4 = 5 ∧ BLBound.bEll 19 5 = 5 ∧
    ∀ m, 4 ≤ m → 5 ≤ BLBound.bEll 19 m := by
  obtain ⟨hUB, hDB⟩ := ub_db (ℓ := 19) (by norm_num) (by norm_num)
  obtain ⟨κ, hκ, hser⟩ := L_padic (ℓ := 19) (by norm_num) (by norm_num) (by norm_num) Cert19.h24 10
    Cert19.f Cert19.form_f Cert19.coeff_zero_f coeff_one_19 Cert19.rank_one Cert19.two_step hUB hDB
  obtain ⟨y, hy, hL⟩ := Cert19.rank_one 3 (by norm_num)
  exact five_of (by norm_num) κ (by rw [toZMod_kappa κ 10 hκ]; decide) hser
    (unit_coeff_b 3 _ y hy hL coeff_one_19)
    (fail_of_detOkG Cert19.h24 3 4 260642 2991954 8 6 22 17 21 46 22 1429 8288 515854 2991953
      (by norm_num) (by norm_num) (by norm_num [x]) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [PartitionPrefix.pentLow])
      (by norm_num [eB, ek]) (by norm_num [eB, ek]) (by norm_num [eB, ek]) (by norm_num [eB, ek])
      (by norm_num) cert19)
    SmallThreshold.bEll_19.2.2.2

/-- **`b₂₃(4) = b₂₃(5) = 5`.** -/
theorem bEll_23 : BLBound.bEll 23 4 = 5 ∧ BLBound.bEll 23 5 = 5 ∧
    ∀ m, 4 ≤ m → 5 ≤ BLBound.bEll 23 m := by
  obtain ⟨hUB, hDB⟩ := ub_db (ℓ := 23) (by norm_num) (by norm_num)
  obtain ⟨κ, hκ, hser⟩ := L_padic (ℓ := 23) (by norm_num) (by norm_num) (by norm_num) Cert23.h24 5
    Cert23.f Cert23.form_f Cert23.coeff_zero_f coeff_one_23 Cert23.rank_one Cert23.two_step hUB hDB
  obtain ⟨y, hy, hL⟩ := Cert23.rank_one 3 (by norm_num)
  exact five_of (by norm_num) κ (by rw [toZMod_kappa κ 5 hκ]; decide) hser
    (unit_coeff_b 3 _ y hy hL coeff_one_23)
    (fail_of_detOkG Cert23.h24 3 4 279841 6704525 8 9 23 19 21 45 23 507 12674 268181 6704524
      (by norm_num) (by norm_num) (by norm_num [x]) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [PartitionPrefix.pentLow])
      (by norm_num [eB, ek]) (by norm_num [eB, ek]) (by norm_num [eB, ek]) (by norm_num [eB, ek])
      (by norm_num) cert23)
    SmallThreshold.bEll_23.2.2.2

end RamanujanTau.FiniteArithmetic.SmallThresholdFive
