import RamanujanTau.FiniteArithmetic.AllPowers29

/-! The normalized odd errors remain in the second Katz envelope. -/
set_option autoImplicit false
namespace RamanujanTau.FiniteArithmetic.Divided29
open PowerSeries BoylanWebb AtkinOBrien AtkinOBrienFinal AllPowers29

lemma B_mono (F : PS 29) (hF : F ∈ B 1) : F ∈ B 2 := by
  refine ⟨⟨hF.1.1, fun N => ?_⟩, hF.2⟩
  obtain ⟨I, a, ha, hd, he⟩ := hF.1.2 N
  exact ⟨I, a, ha, hd, fun i => Dvd_mono (by omega) (he i)⟩

theorem odd_padic_mem : ∃ κ : ℤ_[29], (∃ d : ℤ_[29], κ = 3 + 29 * d) ∧
    ∀ n : ℕ, ∃ G ∈ B 2,
      Ll 29 (2 * n + 3) - κ • Ll 29 (2 * n + 1) = (29 : ℤ_[29]) ^ (n + 1) • G := by
  let O : ℕ → PS 29 := fun b => Ll 29 (2 * b - 1)
  have hO (n : ℕ) : O (n + 1) = Ll 29 (2 * n + 1) := by
    dsimp [O]; congr 1
  have hrec (b : ℕ) (hb : 1 ≤ b) : O (b + 1) = Xop (O b) := by
    obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
    rw [hO, hO, odd_succ]
  have hmem (b : ℕ) (hb : 1 ≤ b) : O b ∈ B 1 := by
    obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
    rw [hO]; exact odd_mem n
  have hlead (b : ℕ) (hb : 1 ≤ b) (F : PS 29) (hF : F ∈ B 1) :
      ∃ c : ℤ_[29], ∃ G : PS 29, F = c • O b + (29 : ℤ_[29]) • G := by
    obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
    rw [hO]; exact leading n F hF
  have hbase (b : ℕ) (hb : 1 ≤ b) : Dvd (29 : ℤ_[29]) 1 (O (b + 1) - 3 • O b) := by
    obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
    rw [hO, hO]
    obtain ⟨G, hG⟩ := PS_dvd_of_map (Ll 29 (2 * (n + 1) + 1) - (3 : ℤ_[29]) • Ll 29 (2 * n + 1)) (by
      rw [map_sub, PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C]
      norm_num only [map_ofNat]
      rw [Ll, Ll, map_map_int, map_map_int,
        show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, Partition29.two_step _ (by omega)]
      rw [show C (3 : ZMod 29) = (3 : PowerSeries (ZMod 29)) from map_ofNat _ 3, sub_self])
    exact ⟨G, by simpa only [pow_one] using hG⟩
  obtain ⟨κ, hκ, h⟩ := lift_padic_mem 1 29 3 (fun _ => Xop) O (fun _ => B 1) (fun _ => B 2)
    PS_reg (fun _ => rfl) hrec (fun _ => rfl) hmem (fun _ _ F hF => X_mem F hF)
    hlead (fun _ _ F hF G hFG => B_div F hF G hFG) (fun b hb => B_mono _ (hmem b hb)) hbase
  refine ⟨κ, hκ, fun n => ?_⟩
  have hn := h (n + 1) (by omega)
  rw [hO, hO] at hn
  convert hn using 1


end RamanujanTau.FiniteArithmetic.Divided29
