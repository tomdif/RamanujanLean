import RamanujanTau.BLBound.Threshold
import RamanujanTau.FiniteArithmetic.PartitionPrefix
import RamanujanTau.OrdQuot.Atkin
import RamanujanTau.VLayer.DBQ

/-!
# Boylan–Webb's threshold at 13, 17, 19, 23

For `ℓ ∈ {13, 17, 19, 23}`, with `b_ℓ(m) = BLBound.bEll ℓ m`:

* `bEll ℓ m ≤ 2⌊m/2⌋ + 1` for every `m ≥ 1`. For `m ≥ 3` this is below the general bound `2m - 1`.
  It comes from the Atkin–O'Brien recurrence `ℓ^b ∣ L(b+2) - κ L(b)`, proved unconditionally.
* `3 ≤ bEll ℓ m` for every `m ≥ 2`. No scalar `c` satisfies `ℓ² ∣ L(3) - c L(1)`, which is
  certified by a 2-by-2 determinant of partition numbers modulo `ℓ²`.
* Hence `bEll ℓ 1 = 1` and `bEll ℓ 2 = bEll ℓ 3 = 3`.
-/
set_option autoImplicit false

namespace RamanujanTau.FiniteArithmetic.SmallThreshold

open PowerSeries AtkinOBrien BoylanWebb AtkinOBrienFinal Packed
open MockTheta5.JTP (partitionGF)

section
variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

/-- The unconditional analytic inputs. -/
theorem ub_db (hℓ : 5 ≤ ℓ) (h11 : 11 ≤ ℓ) : UB ℓ hℓ ∧ DB ℓ hℓ := by
  classical
  have hE := QuotE.quotEBound_C_of_ord hℓ (OrdQuot.ordEBound_C' hℓ)
  have hUB := UBSharp.UB_of_E_C hℓ hE
  have hConj := ConjAlg.HConj_C_of_val' hℓ (hE.toQuotValBound _)
  exact ⟨hUB, VLayer.DB_of_UB_HQ hℓ hUB (SharpHQ.HQ_of_conj_C hℓ h11 hConj)⟩

/-- `pser_dvd` with an arbitrary exponent. -/
theorem pser_dvd_gen (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) (κ : ℤ_[ℓ]) (b e : ℕ)
    (h : Dvd (ℓ : ℤ_[ℓ]) e (Ll ℓ (b + 2) - κ • Ll ℓ b)) (m : ℕ) :
    (ℓ : ℤ_[ℓ]) ^ e ∣ ((pZ ((ℓ : ℤ) ^ (b + 2) * m - eB ℓ (b + 2)) : ℤ) : ℤ_[ℓ]) -
      κ * ((pZ ((ℓ : ℤ) ^ b * m - eB ℓ b) : ℤ) : ℤ_[ℓ]) := by
  obtain ⟨Q, hQ, h1, h2⟩ := L_factor h24 b
  obtain ⟨y, hy⟩ := h
  set φ := PowerSeries.map (Int.castRingHom ℤ_[ℓ])
  obtain ⟨u, hu⟩ := hQ.map φ
  have hL : ∀ c, Ll ℓ c = φ (L ℓ c) := fun c => rfl
  rw [hL, hL, h1, h2, map_mul, map_mul, ← hu] at hy
  have hy' : (u : PS ℓ) * (φ (Pser ℓ (b + 2)) - κ • φ (Pser ℓ b)) = (ℓ : ℤ_[ℓ]) ^ e • y := by
    rw [mul_sub, mul_smul_comm]; exact hy
  have hd : φ (Pser ℓ (b + 2)) - κ • φ (Pser ℓ b) = (ℓ : ℤ_[ℓ]) ^ e • (↑u⁻¹ * y) := by
    rw [← mul_smul_comm, ← hy', ← mul_assoc, Units.inv_mul, one_mul]
  have := congrArg (coeff m) hd
  rw [map_sub, coeff_smul, coeff_smul, coeff_map, coeff_map, Pser, Pser, coeff_mk, coeff_mk,
    smul_eq_mul, smul_eq_mul] at this
  exact ⟨_, by rw [eq_intCast, eq_intCast] at this; exact this⟩

lemma pZ_nat (n : ℕ) : pZ (n : ℤ) = coeff n partitionGF := by
  simp [pZ]

/-- The determinant certificate. -/
def detOk (Q N J i1 i2 j1 j2 : ℕ) : Bool :=
  match PartitionPrefix.pgfPrefix Q N J with
  | some B => (lane B i1 * lane B j2) % Q != (lane B i2 * lane B j1) % Q
  | none => false

/-- **No scalar recurrence from `b = 1` modulo `ℓ²`**, from a determinant certificate. -/
theorem fail_of_detOk (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) (N J i1 i2 j1 j2 : ℕ)
    (hQ : ℓ ^ 2 ≤ 2 ^ 21) (hN0 : 0 < N) (hN : N ≤ 2 ^ 16) (hJ : N ≤ PartitionPrefix.pentLow J)
    (hi1 : (ℓ : ℤ) ^ 1 * (1 : ℕ) - eB ℓ 1 = i1) (hi2 : (ℓ : ℤ) ^ 1 * (2 : ℕ) - eB ℓ 1 = i2)
    (hj1 : (ℓ : ℤ) ^ (1 + 2) * (1 : ℕ) - eB ℓ (1 + 2) = j1)
    (hj2 : (ℓ : ℤ) ^ (1 + 2) * (2 : ℕ) - eB ℓ (1 + 2) = j2)
    (hlt : i1 < N ∧ i2 < N ∧ j1 < N ∧ j2 < N)
    (hok : detOk (ℓ ^ 2) N J i1 i2 j1 j2 = true) (c : ℤ_[ℓ]) :
    ¬ Dvd (ℓ : ℤ_[ℓ]) 2 (Ll ℓ 3 - c • Ll ℓ 1) := by
  intro hc
  unfold detOk at hok
  cases hB : PartitionPrefix.pgfPrefix (ℓ ^ 2) N J with
  | none => rw [hB] at hok; exact absurd hok (by simp)
  | some B =>
    rw [hB] at hok
    have hne : (lane B i1 * lane B j2) % (ℓ ^ 2) ≠ (lane B i2 * lane B j1) % (ℓ ^ 2) := by
      simpa using hok
    have hQ1 : 1 ≤ ℓ ^ 2 := Nat.one_le_pow _ _ hℓp.out.pos
    have hcoeff := PartitionPrefix.coeff_pgf hQ1 hQ hN0 hN hJ hB
    -- Reduce the two divisibilities modulo `ℓ²`.
    have hrel : ∀ (m : ℕ) (a b : ℕ), (ℓ : ℤ) ^ (1 + 2) * m - eB ℓ (1 + 2) = a →
        (ℓ : ℤ) ^ 1 * m - eB ℓ 1 = b → a < N → b < N →
        (lane B a : ZMod (ℓ ^ 2)) = PadicInt.toZModPow 2 c * (lane B b : ZMod (ℓ ^ 2)) := by
      intro m a b ha hb haN hbN
      obtain ⟨y, hy⟩ := pser_dvd_gen h24 c 1 2 hc m
      have h := congrArg (PadicInt.toZModPow (p := ℓ) 2) hy
      rw [ha, hb, pZ_nat, pZ_nat, map_sub, map_mul, map_mul, map_intCast, map_intCast, map_pow,
        map_natCast, ← Nat.cast_pow, ZMod.natCast_self, zero_mul, sub_eq_zero] at h
      rw [← hcoeff a haN, ← hcoeff b hbN]
      exact h
    have e1 := hrel 1 j1 i1 hj1 hi1 hlt.2.2.1 hlt.1
    have e2 := hrel 2 j2 i2 hj2 hi2 hlt.2.2.2 hlt.2.1
    apply hne
    rw [← ZMod.natCast_eq_natCast_iff']
    push_cast
    rw [e1, e2]
    ring

/-- Unit coefficient of `L(1)` from the rank-one reduction. -/
theorem unit_coeff (f : PowerSeries ℤ) (x : ZMod ℓ) (hx : x ≠ 0)
    (hL : Ψ ℓ (L ℓ 1) = C x * Ψ ℓ f) (hf : coeff 1 (Ψ ℓ f) ≠ 0) :
    PadicInt.toZMod (coeff 1 (Ll ℓ (2 * 0 + 1))) ≠ 0 := by
  have h : PadicInt.toZMod (coeff 1 (Ll ℓ 1)) = coeff 1 (Ψ ℓ (L ℓ 1)) := by
    rw [Ll, coeff_map, Ψ, coeff_map]
    simp
  rw [show 2 * 0 + 1 = 1 from rfl, h, hL, coeff_C_mul]
  exact mul_ne_zero hx hf

/-- **Assembly.** -/
theorem threshold_of (h13 : 13 ≤ ℓ) (κ : ℤ_[ℓ]) (hκ : PadicInt.toZMod κ ≠ 0)
    (hser : ∀ b, 1 ≤ b → Dvd (ℓ : ℤ_[ℓ]) b (Ll ℓ (b + 2) - κ • Ll ℓ b))
    (hunit : PadicInt.toZMod (coeff 1 (Ll ℓ (2 * 0 + 1))) ≠ 0)
    (hfail : ∀ c : ℤ_[ℓ], ¬ Dvd (ℓ : ℤ_[ℓ]) 2 (Ll ℓ 3 - c • Ll ℓ 1)) (m : ℕ) (hm : 1 ≤ m) :
    (2 ≤ m → 3 ≤ BLBound.bEll ℓ m) ∧ BLBound.bEll ℓ m ≤ 2 * (m / 2) + 1 := by
  have hodd : ∀ j, Dvd (ℓ : ℤ_[ℓ]) (2 * j + 1)
      (Ll ℓ (2 * j + 3) - κ • Ll ℓ (2 * j + 1)) := fun j => hser (2 * j + 1) (by omega)
  have hupper : 2 * (m / 2) + 1 ∈ BLBound.bSet ℓ m :=
    BLBound.mem_bSet_of_scalar m (m / 2) κ hκ fun j hj => Dvd_mono (by omega) (hodd j)
  refine ⟨fun hm2 => ?_, Nat.sInf_le hupper⟩
  have hlater : ∀ j, Dvd (ℓ : ℤ_[ℓ]) 2
      (Ll ℓ (2 * (0 + 1 + j) + 1) - κ ^ j • Ll ℓ (2 * (0 + 1) + 1)) := by
    intro j
    induction j with
    | zero => exact ⟨0, by simp⟩
    | succ j ih =>
      have he : Ll ℓ (2 * (0 + 1 + (j + 1)) + 1) - κ ^ (j + 1) • Ll ℓ (2 * (0 + 1) + 1) =
          (Ll ℓ (2 * (1 + j) + 3) - κ • Ll ℓ (2 * (1 + j) + 1)) +
            κ • (Ll ℓ (2 * (0 + 1 + j) + 1) - κ ^ j • Ll ℓ (2 * (0 + 1) + 1)) := by
        rw [show 2 * (0 + 1 + (j + 1)) + 1 = 2 * (1 + j) + 3 by ring,
          show 0 + 1 + j = 1 + j by ring, smul_sub, smul_smul, pow_succ', ]
        abel
      rw [he]
      exact Dvd_add (Dvd_mono (by omega) (hodd (1 + j))) (Dvd_smul _ ih)
  have hone : Dvd (ℓ : ℤ_[ℓ]) 1 (Ll ℓ (2 * (0 + 1) + 1) - κ • Ll ℓ (2 * 0 + 1)) := hser 1 le_rfl
  have hnot := BLBound.not_mem_of_scalar κ 0 2 m hm2 hlater hone 1 hunit
    (fun c => by simpa using hfail c)
  have h1 : 1 ∉ BLBound.bSet ℓ m := BLBound.not_mem_bSet h13 m hm 0 (by simpa using hnot)
  have hne : (BLBound.bSet ℓ m).Nonempty := ⟨_, hupper⟩
  obtain ⟨⟨k, hk⟩, -⟩ := Nat.sInf_mem hne
  have hmem := Nat.sInf_mem hne
  unfold BLBound.bEll
  by_contra hlt
  have : sInf (BLBound.bSet ℓ m) = 1 := by omega
  exact h1 (this ▸ hmem)

/-- Exact values at `m ≤ 3`. -/
theorem exact_of (h13 : 13 ≤ ℓ) (κ : ℤ_[ℓ]) (hκ : PadicInt.toZMod κ ≠ 0)
    (hser : ∀ b, 1 ≤ b → Dvd (ℓ : ℤ_[ℓ]) b (Ll ℓ (b + 2) - κ • Ll ℓ b))
    (hunit : PadicInt.toZMod (coeff 1 (Ll ℓ (2 * 0 + 1))) ≠ 0)
    (hfail : ∀ c : ℤ_[ℓ], ¬ Dvd (ℓ : ℤ_[ℓ]) 2 (Ll ℓ 3 - c • Ll ℓ 1)) :
    BLBound.bEll ℓ 1 = 1 ∧ BLBound.bEll ℓ 2 = 3 ∧ BLBound.bEll ℓ 3 = 3 ∧
      ∀ m, 1 ≤ m → (2 ≤ m → 3 ≤ BLBound.bEll ℓ m) ∧ BLBound.bEll ℓ m ≤ 2 * (m / 2) + 1 := by
  have h := threshold_of h13 κ hκ hser hunit hfail
  have h1 := (h 1 le_rfl).2
  have h2 := h 2 (by norm_num)
  have h3 := h 3 (by norm_num)
  have hb1 : 1 ≤ BLBound.bEll ℓ 1 := by
    have hne : (BLBound.bSet ℓ 1).Nonempty :=
      ⟨_, BLBound.mem_bSet (by omega) 1 le_rfl 0 le_rfl⟩
    obtain ⟨⟨k, hk⟩, -⟩ := Nat.sInf_mem hne
    unfold BLBound.bEll
    omega
  refine ⟨by norm_num at h1; omega, ?_, ?_, h⟩
  · have := h2.1 le_rfl; have := h2.2; norm_num at *; omega
  · have := h3.1 (by norm_num); have := h3.2; norm_num at *; omega

lemma toZMod_kappa (κ : ℤ_[ℓ]) (k : ℤ) (hκ : ∃ d : ℤ_[ℓ], κ = (k : ℤ_[ℓ]) + ℓ * d) :
    PadicInt.toZMod κ = (k : ZMod ℓ) := by
  obtain ⟨d, rfl⟩ := hκ
  rw [map_add, map_mul, map_intCast, map_natCast, ZMod.natCast_self, zero_mul, add_zero]

end

/-! ### The four primes -/

theorem cert13 : detOk (13 ^ 2) 3205 100 6 19 1007 3204 = true := by decide +kernel
theorem cert17 : detOk (17 ^ 2) 6347 100 5 22 1433 6346 = true := by decide +kernel
theorem cert19 : detOk (19 ^ 2) 8289 100 4 23 1429 8288 = true := by decide +kernel
theorem cert23 : detOk (23 ^ 2) 12675 100 1 24 507 12674 = true := by decide +kernel

lemma pentLow100 : PartitionPrefix.pentLow 100 = 15251 := by decide

/-- **`b₁₃`.** -/
theorem bEll_13 : BLBound.bEll 13 1 = 1 ∧ BLBound.bEll 13 2 = 3 ∧ BLBound.bEll 13 3 = 3 ∧
    ∀ m, 1 ≤ m → (2 ≤ m → 3 ≤ BLBound.bEll 13 m) ∧ BLBound.bEll 13 m ≤ 2 * (m / 2) + 1 := by
  obtain ⟨hUB, hDB⟩ := ub_db (ℓ := 13) (by norm_num) (by norm_num)
  obtain ⟨κ, hκ, hser⟩ := L_padic (ℓ := 13) (by norm_num) le_rfl (by norm_num) Cert13.h24 6
    Cert13.f Cert13.form_f Cert13.coeff_zero_f coeff_one_13 Cert13.rank_one Cert13.two_step hUB hDB
  obtain ⟨x, hx, hL⟩ := Cert13.rank_one 1 le_rfl
  refine exact_of (by norm_num) κ (by rw [toZMod_kappa κ 6 hκ]; decide) hser
    (unit_coeff _ x hx hL coeff_one_13) (fail_of_detOk Cert13.h24 3205 100 6 19 1007 3204
      (by norm_num) (by norm_num) (by norm_num) (by rw [pentLow100]; norm_num)
      (by norm_num [eB, ek]) (by norm_num [eB, ek]) (by norm_num [eB, ek]) (by norm_num [eB, ek])
      (by norm_num) cert13)

/-- **`b₁₇`.** -/
theorem bEll_17 : BLBound.bEll 17 1 = 1 ∧ BLBound.bEll 17 2 = 3 ∧ BLBound.bEll 17 3 = 3 ∧
    ∀ m, 1 ≤ m → (2 ≤ m → 3 ≤ BLBound.bEll 17 m) ∧ BLBound.bEll 17 m ≤ 2 * (m / 2) + 1 := by
  obtain ⟨hUB, hDB⟩ := ub_db (ℓ := 17) (by norm_num) (by norm_num)
  obtain ⟨κ, hκ, hser⟩ := L_padic (ℓ := 17) (by norm_num) (by norm_num) (by norm_num) Cert17.h24 6
    Cert17.f Cert17.form_f Cert17.coeff_zero_f coeff_one_17 Cert17.rank_one Cert17.two_step hUB hDB
  obtain ⟨x, hx, hL⟩ := Cert17.rank_one 1 le_rfl
  refine exact_of (by norm_num) κ (by rw [toZMod_kappa κ 6 hκ]; decide) hser
    (unit_coeff _ x hx hL coeff_one_17) (fail_of_detOk Cert17.h24 6347 100 5 22 1433 6346
      (by norm_num) (by norm_num) (by norm_num) (by rw [pentLow100]; norm_num)
      (by norm_num [eB, ek]) (by norm_num [eB, ek]) (by norm_num [eB, ek]) (by norm_num [eB, ek])
      (by norm_num) cert17)

/-- **`b₁₉`.** -/
theorem bEll_19 : BLBound.bEll 19 1 = 1 ∧ BLBound.bEll 19 2 = 3 ∧ BLBound.bEll 19 3 = 3 ∧
    ∀ m, 1 ≤ m → (2 ≤ m → 3 ≤ BLBound.bEll 19 m) ∧ BLBound.bEll 19 m ≤ 2 * (m / 2) + 1 := by
  obtain ⟨hUB, hDB⟩ := ub_db (ℓ := 19) (by norm_num) (by norm_num)
  obtain ⟨κ, hκ, hser⟩ := L_padic (ℓ := 19) (by norm_num) (by norm_num) (by norm_num) Cert19.h24 10
    Cert19.f Cert19.form_f Cert19.coeff_zero_f coeff_one_19 Cert19.rank_one Cert19.two_step hUB hDB
  obtain ⟨x, hx, hL⟩ := Cert19.rank_one 1 le_rfl
  refine exact_of (by norm_num) κ (by rw [toZMod_kappa κ 10 hκ]; decide) hser
    (unit_coeff _ x hx hL coeff_one_19) (fail_of_detOk Cert19.h24 8289 100 4 23 1429 8288
      (by norm_num) (by norm_num) (by norm_num) (by rw [pentLow100]; norm_num)
      (by norm_num [eB, ek]) (by norm_num [eB, ek]) (by norm_num [eB, ek]) (by norm_num [eB, ek])
      (by norm_num) cert19)

/-- **`b₂₃`.** -/
theorem bEll_23 : BLBound.bEll 23 1 = 1 ∧ BLBound.bEll 23 2 = 3 ∧ BLBound.bEll 23 3 = 3 ∧
    ∀ m, 1 ≤ m → (2 ≤ m → 3 ≤ BLBound.bEll 23 m) ∧ BLBound.bEll 23 m ≤ 2 * (m / 2) + 1 := by
  obtain ⟨hUB, hDB⟩ := ub_db (ℓ := 23) (by norm_num) (by norm_num)
  obtain ⟨κ, hκ, hser⟩ := L_padic (ℓ := 23) (by norm_num) (by norm_num) (by norm_num) Cert23.h24 5
    Cert23.f Cert23.form_f Cert23.coeff_zero_f coeff_one_23 Cert23.rank_one Cert23.two_step hUB hDB
  obtain ⟨x, hx, hL⟩ := Cert23.rank_one 1 le_rfl
  refine exact_of (by norm_num) κ (by rw [toZMod_kappa κ 5 hκ]; decide) hser
    (unit_coeff _ x hx hL coeff_one_23) (fail_of_detOk Cert23.h24 12675 100 1 24 507 12674
      (by norm_num) (by norm_num) (by norm_num) (by rw [pentLow100]; norm_num)
      (by norm_num [eB, ek]) (by norm_num [eB, ek]) (by norm_num [eB, ek]) (by norm_num [eB, ek])
      (by norm_num) cert23)

end RamanujanTau.FiniteArithmetic.SmallThreshold
