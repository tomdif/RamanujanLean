import RamanujanTau.FiniteArithmetic.ExactAtkin13
import RamanujanTau.FiniteArithmetic.ExactAtkin17
import RamanujanTau.FiniteArithmetic.ExactAtkin19
import RamanujanTau.FiniteArithmetic.ExactAtkin23
import RamanujanTau.FiniteArithmetic.SmallThresholdFive

/-!
# Boylan–Webb's threshold at 13, 17, 19, 23 at every precision

`ExactAtkin{13,17,19,23}.exact`: for every `b ≥ 1`, no scalar `c` gives
`ℓ^(b+1) ∣ L(b+2) − c L(b)`; the Atkin–O'Brien index `b` is exact.

Hence, for Boylan–Webb's literal invariant, `b_ℓ(m) = 2⌊m/2⌋ + 1` for every `m ≥ 1`
(`bEll_13`, …, `bEll_23`).
-/
set_option autoImplicit false

namespace RamanujanTau.FiniteArithmetic.AtkinExact

open PowerSeries AtkinOBrien BoylanWebb AtkinOBrienFinal SmallThreshold SmallThresholdFive

section
variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

/-- **Assembly**: exactness at every odd index gives `b_ℓ(m) = 2⌊m/2⌋ + 1`. -/
theorem bEll_of_exact (h13 : 13 ≤ ℓ) (κ : ℤ_[ℓ]) (hκ : PadicInt.toZMod κ ≠ 0)
    (hser : ∀ b, 1 ≤ b → Dvd (ℓ : ℤ_[ℓ]) b (Ll ℓ (b + 2) - κ • Ll ℓ b))
    (hunit : ∀ k, PadicInt.toZMod (coeff 1 (Ll ℓ (2 * k + 1))) ≠ 0)
    (hexact : ∀ b, 1 ≤ b → ∀ c : ℤ_[ℓ], ¬ Dvd (ℓ : ℤ_[ℓ]) (b + 1) (Ll ℓ (b + 2) - c • Ll ℓ b))
    (m : ℕ) (hm : 1 ≤ m) : BLBound.bEll ℓ m = 2 * (m / 2) + 1 := by
  have hodd : ∀ j, Dvd (ℓ : ℤ_[ℓ]) (2 * j + 1)
      (Ll ℓ (2 * j + 3) - κ • Ll ℓ (2 * j + 1)) := fun j => hser (2 * j + 1) (by omega)
  have hupper : 2 * (m / 2) + 1 ∈ BLBound.bSet ℓ m :=
    BLBound.mem_bSet_of_scalar m (m / 2) κ hκ fun j hj => Dvd_mono (by omega) (hodd j)
  have hnot : ∀ k, k < m / 2 → 2 * k + 1 ∉ BLBound.bSet ℓ m := by
    intro k hk
    have h := BLBound.not_mem_of_scalar κ k (2 * k + 2) m (by omega)
      (later κ hser k (2 * k + 2) (by omega)) (Dvd_mono (by omega) (hser (2 * k + 1) (by omega)))
      1 (hunit k) (fun c => by
        have := hexact (2 * k + 1) (by omega) c
        rwa [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring, show 2 * k + 2 = 2 * k + 1 + 1 by ring])
    exact BLBound.not_mem_bSet h13 m hm k h
  have hne : (BLBound.bSet ℓ m).Nonempty := ⟨_, hupper⟩
  have hmem := Nat.sInf_mem hne
  have hle : BLBound.bEll ℓ m ≤ 2 * (m / 2) + 1 := Nat.sInf_le hupper
  obtain ⟨⟨r, hr⟩, -⟩ := hmem
  unfold BLBound.bEll at hle ⊢
  by_contra hneq
  have hlt : r < m / 2 := by omega
  exact hnot r hlt (hr ▸ Nat.sInf_mem hne)

end

/-- **`b₁₃(m) = 2⌊m/2⌋ + 1` for every `m ≥ 1`.** -/
theorem bEll_13 (m : ℕ) (hm : 1 ≤ m) : BLBound.bEll 13 m = 2 * (m / 2) + 1 := by
  obtain ⟨hUB, hDB⟩ := ub_db (ℓ := 13) (by norm_num) (by norm_num)
  obtain ⟨κ, hκ, hser⟩ := L_padic (ℓ := 13) (by norm_num) le_rfl (by norm_num) Cert13.h24 6
    Cert13.f Cert13.form_f Cert13.coeff_zero_f coeff_one_13 Cert13.rank_one Cert13.two_step hUB hDB
  refine bEll_of_exact (by norm_num) κ (by rw [toZMod_kappa κ 6 hκ]; decide) hser (fun k => ?_)
    ExactAtkin13.exact m hm
  obtain ⟨y, hy, hL⟩ := Cert13.rank_one (2 * k + 1) (by omega)
  exact unit_coeff_b _ _ y hy hL coeff_one_13

/-- **`b₁₇(m) = 2⌊m/2⌋ + 1` for every `m ≥ 1`.** -/
theorem bEll_17 (m : ℕ) (hm : 1 ≤ m) : BLBound.bEll 17 m = 2 * (m / 2) + 1 := by
  obtain ⟨hUB, hDB⟩ := ub_db (ℓ := 17) (by norm_num) (by norm_num)
  obtain ⟨κ, hκ, hser⟩ := L_padic (ℓ := 17) (by norm_num) (by norm_num) (by norm_num) Cert17.h24 6
    Cert17.f Cert17.form_f Cert17.coeff_zero_f coeff_one_17 Cert17.rank_one Cert17.two_step hUB hDB
  refine bEll_of_exact (by norm_num) κ (by rw [toZMod_kappa κ 6 hκ]; decide) hser (fun k => ?_)
    ExactAtkin17.exact m hm
  obtain ⟨y, hy, hL⟩ := Cert17.rank_one (2 * k + 1) (by omega)
  exact unit_coeff_b _ _ y hy hL coeff_one_17

/-- **`b₁₉(m) = 2⌊m/2⌋ + 1` for every `m ≥ 1`.** -/
theorem bEll_19 (m : ℕ) (hm : 1 ≤ m) : BLBound.bEll 19 m = 2 * (m / 2) + 1 := by
  obtain ⟨hUB, hDB⟩ := ub_db (ℓ := 19) (by norm_num) (by norm_num)
  obtain ⟨κ, hκ, hser⟩ := L_padic (ℓ := 19) (by norm_num) (by norm_num) (by norm_num) Cert19.h24 10
    Cert19.f Cert19.form_f Cert19.coeff_zero_f coeff_one_19 Cert19.rank_one Cert19.two_step hUB hDB
  refine bEll_of_exact (by norm_num) κ (by rw [toZMod_kappa κ 10 hκ]; decide) hser (fun k => ?_)
    ExactAtkin19.exact m hm
  obtain ⟨y, hy, hL⟩ := Cert19.rank_one (2 * k + 1) (by omega)
  exact unit_coeff_b _ _ y hy hL coeff_one_19

/-- **`b₂₃(m) = 2⌊m/2⌋ + 1` for every `m ≥ 1`.** -/
theorem bEll_23 (m : ℕ) (hm : 1 ≤ m) : BLBound.bEll 23 m = 2 * (m / 2) + 1 := by
  obtain ⟨hUB, hDB⟩ := ub_db (ℓ := 23) (by norm_num) (by norm_num)
  obtain ⟨κ, hκ, hser⟩ := L_padic (ℓ := 23) (by norm_num) (by norm_num) (by norm_num) Cert23.h24 5
    Cert23.f Cert23.form_f Cert23.coeff_zero_f coeff_one_23 Cert23.rank_one Cert23.two_step hUB hDB
  refine bEll_of_exact (by norm_num) κ (by rw [toZMod_kappa κ 5 hκ]; decide) hser (fun k => ?_)
    ExactAtkin23.exact m hm
  obtain ⟨y, hy, hL⟩ := Cert23.rank_one (2 * k + 1) (by omega)
  exact unit_coeff_b _ _ y hy hL coeff_one_23

end RamanujanTau.FiniteArithmetic.AtkinExact
