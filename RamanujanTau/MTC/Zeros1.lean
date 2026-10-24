/-
# HM Theorem 0.3 for `f_{3,7,3}` at the MTC₁ point

`q = t^{42}`, `y₁ = −i t^{189} = Z⁶³ t^{189}`, `x₁ = i t^{189} = Z²¹ t^{189}`. As for MTC₀ (`Zeros373`): `F` vanishes at
the 49 zeros of the `j(B_s)` and 7 zeros of the `j(A_r)`, pairwise inequivalent under `x ↦ q^{40}x`, so `F = 0`.
-/
import RamanujanTau.MTC.Zeros373

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset

/-- the auxiliary series at `y₁`. -/
noncomputable abbrev F1 : ℤ → L := FS hq42 189 (Z84 ^ (63 : ℤ))

theorem zB0' (j : ℤ) : ev F1 (-3) (Z84 ^ (3 + 12 * j)) = 0 := by
  have hcx : Z84 ^ (3 + 12 * j) ≠ 0 := zpow_ne_zero _ Z_ne
  have hB : eBT (qe := 42) 189 0 (-3) = 160 * ((42 : ℕ) : ℤ) * 0 := by norm_num [eBT]
  have hc : cBT (Z84 ^ (63 : ℤ)) (Z84 ^ (3 + 12 * j)) = 1 := by
    unfold cBT; zsimp; exact Z_eq_one (by omega)
  unfold F1
  rw [FS_ev_B hq42 189 _ (s0 := 0) (ℓ0 := 0) (t1 := 2) (k1 := 1) hB hc hcx hcy0 (by decide)
      ⟨by norm_num, by norm_num⟩ (by decide) (by decide),
    brB_zero hq42 189 _ hB hc hcx hcy0 (by norm_num) (fun r hr => by
      simp only [Finset.mem_Icc] at hr
      obtain ⟨h0, h3⟩ := hr
      interval_cases r <;>
      · simp only [sig1, dmon, Msh, mono_mul]
        apply mono_add_zero
        · norm_num [eTn, eAT, c2]
        · unfold cTn cAT; zsimp; exact Z_mod (by first | omega | (ring_nf; omega)))]
  simp

theorem zB1' (j : ℤ) : ev F1 (237) (Z84 ^ (3 + 12 * j)) = 0 := by
  have hcx : Z84 ^ (3 + 12 * j) ≠ 0 := zpow_ne_zero _ Z_ne
  have hB : eBT (qe := 42) 189 3 (237) = 160 * ((42 : ℕ) : ℤ) * 1 := by norm_num [eBT]
  have hc : cBT (Z84 ^ (63 : ℤ)) (Z84 ^ (3 + 12 * j)) = 1 := by
    unfold cBT; zsimp; exact Z_eq_one (by omega)
  unfold F1
  rw [FS_ev_B hq42 189 _ (s0 := 3) (ℓ0 := 1) (t1 := 1) (k1 := 1) hB hc hcx hcy0 (by decide)
      ⟨by norm_num, by norm_num⟩ (by decide) (by decide),
    brB_zero hq42 189 _ hB hc hcx hcy0 (by norm_num) (fun r hr => by
      simp only [Finset.mem_Icc] at hr
      obtain ⟨h0, h3⟩ := hr
      interval_cases r <;>
      · simp only [sig1, dmon, Msh, mono_mul]
        apply mono_add_zero
        · norm_num [eTn, eAT, c2]
        · unfold cTn cAT; zsimp; exact Z_mod (by first | omega | (ring_nf; omega)))]
  simp

theorem zB2' (j : ℤ) : ev F1 (477) (Z84 ^ (3 + 12 * j)) = 0 := by
  have hcx : Z84 ^ (3 + 12 * j) ≠ 0 := zpow_ne_zero _ Z_ne
  have hB : eBT (qe := 42) 189 2 (477) = 160 * ((42 : ℕ) : ℤ) * 1 := by norm_num [eBT]
  have hc : cBT (Z84 ^ (63 : ℤ)) (Z84 ^ (3 + 12 * j)) = 1 := by
    unfold cBT; zsimp; exact Z_eq_one (by omega)
  unfold F1
  rw [FS_ev_B hq42 189 _ (s0 := 2) (ℓ0 := 1) (t1 := 0) (k1 := 1) hB hc hcx hcy0 (by decide)
      ⟨by norm_num, by norm_num⟩ (by decide) (by decide),
    brB_zero hq42 189 _ hB hc hcx hcy0 (by norm_num) (fun r hr => by
      simp only [Finset.mem_Icc] at hr
      obtain ⟨h0, h3⟩ := hr
      interval_cases r <;>
      · simp only [sig1, dmon, Msh, mono_mul]
        apply mono_add_zero
        · norm_num [eTn, eAT, c2]
        · unfold cTn cAT; zsimp; exact Z_mod (by first | omega | (ring_nf; omega)))]
  simp

theorem zB3' (j : ℤ) : ev F1 (717) (Z84 ^ (3 + 12 * j)) = 0 := by
  have hcx : Z84 ^ (3 + 12 * j) ≠ 0 := zpow_ne_zero _ Z_ne
  have hB : eBT (qe := 42) 189 1 (717) = 160 * ((42 : ℕ) : ℤ) * 1 := by norm_num [eBT]
  have hc : cBT (Z84 ^ (63 : ℤ)) (Z84 ^ (3 + 12 * j)) = 1 := by
    unfold cBT; zsimp; exact Z_eq_one (by omega)
  unfold F1
  rw [FS_ev_B hq42 189 _ (s0 := 1) (ℓ0 := 1) (t1 := 2) (k1 := 2) hB hc hcx hcy0 (by decide)
      ⟨by norm_num, by norm_num⟩ (by decide) (by decide),
    brB_zero hq42 189 _ hB hc hcx hcy0 (by norm_num) (fun r hr => by
      simp only [Finset.mem_Icc] at hr
      obtain ⟨h0, h3⟩ := hr
      interval_cases r <;>
      · simp only [sig1, dmon, Msh, mono_mul]
        apply mono_add_zero
        · norm_num [eTn, eAT, c2]
        · unfold cTn cAT; zsimp; exact Z_mod (by first | omega | (ring_nf; omega)))]
  simp

theorem zB4' (j : ℤ) : ev F1 (957) (Z84 ^ (3 + 12 * j)) = 0 := by
  have hcx : Z84 ^ (3 + 12 * j) ≠ 0 := zpow_ne_zero _ Z_ne
  have hB : eBT (qe := 42) 189 0 (957) = 160 * ((42 : ℕ) : ℤ) * 1 := by norm_num [eBT]
  have hc : cBT (Z84 ^ (63 : ℤ)) (Z84 ^ (3 + 12 * j)) = 1 := by
    unfold cBT; zsimp; exact Z_eq_one (by omega)
  unfold F1
  rw [FS_ev_B hq42 189 _ (s0 := 0) (ℓ0 := 1) (t1 := 1) (k1 := 2) hB hc hcx hcy0 (by decide)
      ⟨by norm_num, by norm_num⟩ (by decide) (by decide),
    brB_zero hq42 189 _ hB hc hcx hcy0 (by norm_num) (fun r hr => by
      simp only [Finset.mem_Icc] at hr
      obtain ⟨h0, h3⟩ := hr
      interval_cases r <;>
      · simp only [sig1, dmon, Msh, mono_mul]
        apply mono_add_zero
        · norm_num [eTn, eAT, c2]
        · unfold cTn cAT; zsimp; exact Z_mod (by first | omega | (ring_nf; omega)))]
  simp

theorem zB5' (j : ℤ) : ev F1 (1197) (Z84 ^ (3 + 12 * j)) = 0 := by
  have hcx : Z84 ^ (3 + 12 * j) ≠ 0 := zpow_ne_zero _ Z_ne
  have hB : eBT (qe := 42) 189 3 (1197) = 160 * ((42 : ℕ) : ℤ) * 2 := by norm_num [eBT]
  have hc : cBT (Z84 ^ (63 : ℤ)) (Z84 ^ (3 + 12 * j)) = 1 := by
    unfold cBT; zsimp; exact Z_eq_one (by omega)
  unfold F1
  rw [FS_ev_B hq42 189 _ (s0 := 3) (ℓ0 := 2) (t1 := 0) (k1 := 2) hB hc hcx hcy0 (by decide)
      ⟨by norm_num, by norm_num⟩ (by decide) (by decide),
    brB_zero hq42 189 _ hB hc hcx hcy0 (by norm_num) (fun r hr => by
      simp only [Finset.mem_Icc] at hr
      obtain ⟨h0, h3⟩ := hr
      interval_cases r <;>
      · simp only [sig1, dmon, Msh, mono_mul]
        apply mono_add_zero
        · norm_num [eTn, eAT, c2]
        · unfold cTn cAT; zsimp; exact Z_mod (by first | omega | (ring_nf; omega)))]
  simp

theorem zB6' (j : ℤ) : ev F1 (1437) (Z84 ^ (3 + 12 * j)) = 0 := by
  have hcx : Z84 ^ (3 + 12 * j) ≠ 0 := zpow_ne_zero _ Z_ne
  have hB : eBT (qe := 42) 189 2 (1437) = 160 * ((42 : ℕ) : ℤ) * 2 := by norm_num [eBT]
  have hc : cBT (Z84 ^ (63 : ℤ)) (Z84 ^ (3 + 12 * j)) = 1 := by
    unfold cBT; zsimp; exact Z_eq_one (by omega)
  unfold F1
  rw [FS_ev_B hq42 189 _ (s0 := 2) (ℓ0 := 2) (t1 := 2) (k1 := 3) hB hc hcx hcy0 (by decide)
      ⟨by norm_num, by norm_num⟩ (by decide) (by decide),
    brB_zero hq42 189 _ hB hc hcx hcy0 (by norm_num) (fun r hr => by
      simp only [Finset.mem_Icc] at hr
      obtain ⟨h0, h3⟩ := hr
      interval_cases r <;>
      · simp only [sig1, dmon, Msh, mono_mul]
        apply mono_add_zero
        · norm_num [eTn, eAT, c2]
        · unfold cTn cAT; zsimp; exact Z_mod (by first | omega | (ring_nf; omega)))]
  simp

theorem zA0' (j : ℤ) : ev F1 (637) (Z84 ^ (7 + 28 * j)) = 0 := by
  have hcx : Z84 ^ (7 + 28 * j) ≠ 0 := zpow_ne_zero _ Z_ne
  have hA : eAT (qe := 42) 189 0 (637) = 160 * ((42 : ℕ) : ℤ) * 0 := by norm_num [eAT]
  have hc : cAT (Z84 ^ (63 : ℤ)) (Z84 ^ (7 + 28 * j)) = 1 := by
    unfold cAT; zsimp; exact Z_eq_one (by omega)
  unfold F1
  rw [FS_ev_A hq42 189 _ (r0 := 0) (ℓ0 := 0) (t1 := 2) (k1 := 1) hA hc hcx hcy0 (by decide)
      ⟨by norm_num, by norm_num⟩ (by decide) (by decide),
    brA_zero hq42 189 _ hA hc hcx hcy0 (by norm_num) (fun s hs => by
      simp only [Finset.mem_Icc] at hs
      obtain ⟨h0, h3⟩ := hs
      interval_cases s <;>
      · simp only [SA, sig2, dmon, Msh, mono_mul]
        apply mono_add_zero
        · norm_num [eTn, eBT, c2]
        · unfold cTn cBT; zsimp; exact Z_mod (by first | omega | (ring_nf; omega)))]
  simp

theorem zA1' (j : ℤ) : ev F1 (1197) (Z84 ^ (7 + 28 * j)) = 0 := by
  have hcx : Z84 ^ (7 + 28 * j) ≠ 0 := zpow_ne_zero _ Z_ne
  have hA : eAT (qe := 42) 189 1 (1197) = 160 * ((42 : ℕ) : ℤ) * 0 := by norm_num [eAT]
  have hc : cAT (Z84 ^ (63 : ℤ)) (Z84 ^ (7 + 28 * j)) = 1 := by
    unfold cAT; zsimp; exact Z_eq_one (by omega)
  unfold F1
  rw [FS_ev_A hq42 189 _ (r0 := 1) (ℓ0 := 0) (t1 := 0) (k1 := 0) hA hc hcx hcy0 (by decide)
      ⟨by norm_num, by norm_num⟩ (by decide) (by decide),
    brA_zero hq42 189 _ hA hc hcx hcy0 (by norm_num) (fun s hs => by
      simp only [Finset.mem_Icc] at hs
      obtain ⟨h0, h3⟩ := hs
      interval_cases s <;>
      · simp only [SA, sig2, dmon, Msh, mono_mul]
        apply mono_add_zero
        · norm_num [eTn, eBT, c2]
        · unfold cTn cBT; zsimp; exact Z_mod (by first | omega | (ring_nf; omega)))]
  simp

theorem zA2' (j : ℤ) : ev F1 (1757) (Z84 ^ (7 + 28 * j)) = 0 := by
  have hcx : Z84 ^ (7 + 28 * j) ≠ 0 := zpow_ne_zero _ Z_ne
  have hA : eAT (qe := 42) 189 2 (1757) = 160 * ((42 : ℕ) : ℤ) * 0 := by norm_num [eAT]
  have hc : cAT (Z84 ^ (63 : ℤ)) (Z84 ^ (7 + 28 * j)) = 1 := by
    unfold cAT; zsimp; exact Z_eq_one (by omega)
  unfold F1
  rw [FS_ev_A hq42 189 _ (r0 := 2) (ℓ0 := 0) (t1 := 1) (k1 := 0) hA hc hcx hcy0 (by decide)
      ⟨by norm_num, by norm_num⟩ (by decide) (by decide),
    brA_zero hq42 189 _ hA hc hcx hcy0 (by norm_num) (fun s hs => by
      simp only [Finset.mem_Icc] at hs
      obtain ⟨h0, h3⟩ := hs
      interval_cases s <;>
      · simp only [SA, sig2, dmon, Msh, mono_mul]
        apply mono_add_zero
        · norm_num [eTn, eBT, c2]
        · unfold cTn cBT; zsimp; exact Z_mod (by first | omega | (ring_nf; omega)))]
  simp

def peT1 : Fin 56 → ℤ := ![-3, -3, -3, -3, -3, -3, -3, 237, 237, 237, 237, 237, 237, 237, 477, 477, 477, 477, 477, 477, 477, 717, 717, 717, 717, 717, 717, 717, 957, 957, 957, 957, 957, 957, 957, 1197, 1197, 1197, 1197, 1197, 1197, 1197, 1437, 1437, 1437, 1437, 1437, 1437, 1437, 637, 637, 637, 1757, 1757, 1757, 1197]
def pmT1 : Fin 56 → ℤ := ![3 + 12 * 0, 3 + 12 * 1, 3 + 12 * 2, 3 + 12 * 3, 3 + 12 * 4, 3 + 12 * 5, 3 + 12 * 6, 3 + 12 * 0, 3 + 12 * 1, 3 + 12 * 2, 3 + 12 * 3, 3 + 12 * 4, 3 + 12 * 5, 3 + 12 * 6, 3 + 12 * 0, 3 + 12 * 1, 3 + 12 * 2, 3 + 12 * 3, 3 + 12 * 4, 3 + 12 * 5, 3 + 12 * 6, 3 + 12 * 0, 3 + 12 * 1, 3 + 12 * 2, 3 + 12 * 3, 3 + 12 * 4, 3 + 12 * 5, 3 + 12 * 6, 3 + 12 * 0, 3 + 12 * 1, 3 + 12 * 2, 3 + 12 * 3, 3 + 12 * 4, 3 + 12 * 5, 3 + 12 * 6, 3 + 12 * 0, 3 + 12 * 1, 3 + 12 * 2, 3 + 12 * 3, 3 + 12 * 4, 3 + 12 * 5, 3 + 12 * 6, 3 + 12 * 0, 3 + 12 * 1, 3 + 12 * 2, 3 + 12 * 3, 3 + 12 * 4, 3 + 12 * 5, 3 + 12 * 6, 7 + 28 * 0, 7 + 28 * 1, 7 + 28 * 2, 7 + 28 * 0, 7 + 28 * 1, 7 + 28 * 2, 7 + 28 * 0]
noncomputable def pcT1 (i : Fin 56) : ℂ := Z84 ^ pmT1 i

lemma zeros56' (i : Fin 56) : ev F1 (peT1 i) (pcT1 i) = 0 := by
  fin_cases i
  · exact zB0' 0
  · exact zB0' 1
  · exact zB0' 2
  · exact zB0' 3
  · exact zB0' 4
  · exact zB0' 5
  · exact zB0' 6
  · exact zB1' 0
  · exact zB1' 1
  · exact zB1' 2
  · exact zB1' 3
  · exact zB1' 4
  · exact zB1' 5
  · exact zB1' 6
  · exact zB2' 0
  · exact zB2' 1
  · exact zB2' 2
  · exact zB2' 3
  · exact zB2' 4
  · exact zB2' 5
  · exact zB2' 6
  · exact zB3' 0
  · exact zB3' 1
  · exact zB3' 2
  · exact zB3' 3
  · exact zB3' 4
  · exact zB3' 5
  · exact zB3' 6
  · exact zB4' 0
  · exact zB4' 1
  · exact zB4' 2
  · exact zB4' 3
  · exact zB4' 4
  · exact zB4' 5
  · exact zB4' 6
  · exact zB5' 0
  · exact zB5' 1
  · exact zB5' 2
  · exact zB5' 3
  · exact zB5' 4
  · exact zB5' 5
  · exact zB5' 6
  · exact zB6' 0
  · exact zB6' 1
  · exact zB6' 2
  · exact zB6' 3
  · exact zB6' 4
  · exact zB6' 5
  · exact zB6' 6
  · exact zA0' 0
  · exact zA0' 1
  · exact zA0' 2
  · exact zA2' 0
  · exact zA2' 1
  · exact zA2' 2
  · exact zA1' 0

lemma dist56' : ∀ i j : Fin 56, i ≠ j → (peT1 i - peT1 j) % 1680 = 0 → (pmT1 i - pmT1 j) % 84 ≠ 0 := by decide

theorem F1_eq_zero : F1 = 0 := by
  have hn : ‖Z84 ^ (63 : ℤ)‖ = 1 := by rw [norm_zpow, Z_norm, one_zpow]
  exact zero_count (NQ := 40 * 42) (by norm_num) 55 (zpow_ne_zero _ hcy0) (FS_mem_Th hq42 189 _ hn) peT1 pcT1
    (fun i => zpow_ne_zero _ Z_ne)
    (fun i j hij a ha => Z_ne_Z (dist56' i j hij (by rw [ha]; push_cast; omega)))
    zeros56'

theorem Dv_x1 : Dv hq42 189 (Z84 ^ (63 : ℤ)) 189 (Z84 ^ (21 : ℤ)) = 0 := by
  have h := FS_ev hq42 189 _ 189 hcy0 cgood_xstar
  have h0 : ev F1 189 (Z84 ^ (21 : ℤ)) = 0 := by
    rw [F1_eq_zero]; exact ev_zero 189 _
  unfold F1 at h0
  rw [h0] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (Pv_ne hq42 189 _ hcy0 cgood_xstar 189)

/-- **HM Theorem 0.3 for `f_{3,7,3}` at `(x₁, y₁)`**. -/
theorem hm03_x1 :
    Jb hq42 * ev (fS hq42 189 (Z84 ^ (63 : ℤ))) 189 (Z84 ^ (21 : ℤ)) =
      gNum hq42 189 (Z84 ^ (63 : ℤ)) 189 (Z84 ^ (21 : ℤ)) +
        kap (h160 hq42) * thV hq42 189 (Z84 ^ (63 : ℤ)) 189 (Z84 ^ (21 : ℤ)) := by
  have := Dv_x1
  unfold Dv at this
  linear_combination this

end MTC
