/-
# `F = 0` at `(x*, y*)`, hence HM Theorem 0.3 for `f_{3,7,3}` at the MTC₀ specialization point

`q = t^{42}`, `y* = −i t^{105} = Z⁶³ t^{105}`, `x* = i t^{105} = Z²¹ t^{105}` (`Z = e^{πi/42}`).
`F` vanishes at the 49 zeros of the `j(B_s)` and at 7 zeros of the `j(A_r)` (the residue identities
`brB_zero`, `brA_zero`), which are pairwise inequivalent under `x ↦ q^{40}x`; since `F ∈ Th(55)`, `F = 0`.
-/
import RamanujanTau.MTC.EvA373
import RamanujanTau.MTC.Z84

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset

lemma mono_add_zero {E E' : ℤ} {C C' : ℂ} (hE : E = E') (hC : C' = -C) : mono E C + mono E' C' = 0 := by
  subst hE; rw [hC, ← neg_mono]; ring

lemma Pv_ne {qe : ℕ} (hqe : 1 ≤ qe) (ey : ℤ) (cy : ℂ) (hcy : cy ≠ 0) {cx : ℂ} (h : CGood cy cx) (ex : ℤ) :
    Pv hqe ey cy ex cx ≠ 0 := by
  unfold Pv
  refine mul_ne_zero (List.prod_ne_zero ?_) (List.prod_ne_zero ?_) <;>
    simp only [List.mem_map, not_exists, not_and] <;> intro r _ h0
  · exact θ_ne_zero (h160 hqe) (cAT_ne cy h.1 hcy) (fun _ _ => h.2.2.2.1) h0
  · exact θ_ne_zero (h160 hqe) (cBT_ne cy h.1 hcy) (fun _ _ => h.2.2.2.2) h0

/-! ## The specialization -/

lemma hq42 : 1 ≤ 42 := by norm_num

/-- the auxiliary series at `y*`. -/
noncomputable abbrev F0 : ℤ → L := FS hq42 105 (Z84 ^ (63 : ℤ))

lemma hcy0 : Z84 ^ (63 : ℤ) ≠ 0 := zpow_ne_zero _ Z_ne


/-- zeros of `j(B_0)` with `ℓ = 0`. -/
theorem zB0 (j : ℤ) : ev F0 (-39) (Z84 ^ (3 + 12 * j)) = 0 := by
  have hcx : Z84 ^ (3 + 12 * j) ≠ 0 := zpow_ne_zero _ Z_ne
  have hB : eBT (qe := 42) 105 0 (-39) = 160 * ((42 : ℕ) : ℤ) * 0 := by norm_num [eBT]
  have hc : cBT (Z84 ^ (63 : ℤ)) (Z84 ^ (3 + 12 * j)) = 1 := by
    unfold cBT; zsimp; exact Z_eq_one (by omega)
  unfold F0
  rw [FS_ev_B hq42 105 _ (s0 := 0) (ℓ0 := 0) (t1 := 2) (k1 := 1) hB hc hcx hcy0 (by decide)
      ⟨by norm_num, by norm_num⟩ (by decide) (by decide),
    brB_zero hq42 105 _ hB hc hcx hcy0 (by norm_num) (fun r hr => by
      simp only [Finset.mem_Icc] at hr
      obtain ⟨h0, h3⟩ := hr
      interval_cases r <;>
      · simp only [sig1, dmon, Msh, mono_mul]
        apply mono_add_zero
        · norm_num [eTn, eAT, c2]
        · unfold cTn cAT; zsimp; exact Z_mod (by first | omega | (ring_nf; omega)))]
  simp

/-- zeros of `j(B_3)` with `ℓ = 1`. -/
theorem zB1 (j : ℤ) : ev F0 (201) (Z84 ^ (3 + 12 * j)) = 0 := by
  have hcx : Z84 ^ (3 + 12 * j) ≠ 0 := zpow_ne_zero _ Z_ne
  have hB : eBT (qe := 42) 105 3 (201) = 160 * ((42 : ℕ) : ℤ) * 1 := by norm_num [eBT]
  have hc : cBT (Z84 ^ (63 : ℤ)) (Z84 ^ (3 + 12 * j)) = 1 := by
    unfold cBT; zsimp; exact Z_eq_one (by omega)
  unfold F0
  rw [FS_ev_B hq42 105 _ (s0 := 3) (ℓ0 := 1) (t1 := 1) (k1 := 1) hB hc hcx hcy0 (by decide)
      ⟨by norm_num, by norm_num⟩ (by decide) (by decide),
    brB_zero hq42 105 _ hB hc hcx hcy0 (by norm_num) (fun r hr => by
      simp only [Finset.mem_Icc] at hr
      obtain ⟨h0, h3⟩ := hr
      interval_cases r <;>
      · simp only [sig1, dmon, Msh, mono_mul]
        apply mono_add_zero
        · norm_num [eTn, eAT, c2]
        · unfold cTn cAT; zsimp; exact Z_mod (by first | omega | (ring_nf; omega)))]
  simp

/-- zeros of `j(B_2)` with `ℓ = 1`. -/
theorem zB2 (j : ℤ) : ev F0 (441) (Z84 ^ (3 + 12 * j)) = 0 := by
  have hcx : Z84 ^ (3 + 12 * j) ≠ 0 := zpow_ne_zero _ Z_ne
  have hB : eBT (qe := 42) 105 2 (441) = 160 * ((42 : ℕ) : ℤ) * 1 := by norm_num [eBT]
  have hc : cBT (Z84 ^ (63 : ℤ)) (Z84 ^ (3 + 12 * j)) = 1 := by
    unfold cBT; zsimp; exact Z_eq_one (by omega)
  unfold F0
  rw [FS_ev_B hq42 105 _ (s0 := 2) (ℓ0 := 1) (t1 := 0) (k1 := 1) hB hc hcx hcy0 (by decide)
      ⟨by norm_num, by norm_num⟩ (by decide) (by decide),
    brB_zero hq42 105 _ hB hc hcx hcy0 (by norm_num) (fun r hr => by
      simp only [Finset.mem_Icc] at hr
      obtain ⟨h0, h3⟩ := hr
      interval_cases r <;>
      · simp only [sig1, dmon, Msh, mono_mul]
        apply mono_add_zero
        · norm_num [eTn, eAT, c2]
        · unfold cTn cAT; zsimp; exact Z_mod (by first | omega | (ring_nf; omega)))]
  simp

/-- zeros of `j(B_1)` with `ℓ = 1`. -/
theorem zB3 (j : ℤ) : ev F0 (681) (Z84 ^ (3 + 12 * j)) = 0 := by
  have hcx : Z84 ^ (3 + 12 * j) ≠ 0 := zpow_ne_zero _ Z_ne
  have hB : eBT (qe := 42) 105 1 (681) = 160 * ((42 : ℕ) : ℤ) * 1 := by norm_num [eBT]
  have hc : cBT (Z84 ^ (63 : ℤ)) (Z84 ^ (3 + 12 * j)) = 1 := by
    unfold cBT; zsimp; exact Z_eq_one (by omega)
  unfold F0
  rw [FS_ev_B hq42 105 _ (s0 := 1) (ℓ0 := 1) (t1 := 2) (k1 := 2) hB hc hcx hcy0 (by decide)
      ⟨by norm_num, by norm_num⟩ (by decide) (by decide),
    brB_zero hq42 105 _ hB hc hcx hcy0 (by norm_num) (fun r hr => by
      simp only [Finset.mem_Icc] at hr
      obtain ⟨h0, h3⟩ := hr
      interval_cases r <;>
      · simp only [sig1, dmon, Msh, mono_mul]
        apply mono_add_zero
        · norm_num [eTn, eAT, c2]
        · unfold cTn cAT; zsimp; exact Z_mod (by first | omega | (ring_nf; omega)))]
  simp

/-- zeros of `j(B_0)` with `ℓ = 1`. -/
theorem zB4 (j : ℤ) : ev F0 (921) (Z84 ^ (3 + 12 * j)) = 0 := by
  have hcx : Z84 ^ (3 + 12 * j) ≠ 0 := zpow_ne_zero _ Z_ne
  have hB : eBT (qe := 42) 105 0 (921) = 160 * ((42 : ℕ) : ℤ) * 1 := by norm_num [eBT]
  have hc : cBT (Z84 ^ (63 : ℤ)) (Z84 ^ (3 + 12 * j)) = 1 := by
    unfold cBT; zsimp; exact Z_eq_one (by omega)
  unfold F0
  rw [FS_ev_B hq42 105 _ (s0 := 0) (ℓ0 := 1) (t1 := 1) (k1 := 2) hB hc hcx hcy0 (by decide)
      ⟨by norm_num, by norm_num⟩ (by decide) (by decide),
    brB_zero hq42 105 _ hB hc hcx hcy0 (by norm_num) (fun r hr => by
      simp only [Finset.mem_Icc] at hr
      obtain ⟨h0, h3⟩ := hr
      interval_cases r <;>
      · simp only [sig1, dmon, Msh, mono_mul]
        apply mono_add_zero
        · norm_num [eTn, eAT, c2]
        · unfold cTn cAT; zsimp; exact Z_mod (by first | omega | (ring_nf; omega)))]
  simp

/-- zeros of `j(B_3)` with `ℓ = 2`. -/
theorem zB5 (j : ℤ) : ev F0 (1161) (Z84 ^ (3 + 12 * j)) = 0 := by
  have hcx : Z84 ^ (3 + 12 * j) ≠ 0 := zpow_ne_zero _ Z_ne
  have hB : eBT (qe := 42) 105 3 (1161) = 160 * ((42 : ℕ) : ℤ) * 2 := by norm_num [eBT]
  have hc : cBT (Z84 ^ (63 : ℤ)) (Z84 ^ (3 + 12 * j)) = 1 := by
    unfold cBT; zsimp; exact Z_eq_one (by omega)
  unfold F0
  rw [FS_ev_B hq42 105 _ (s0 := 3) (ℓ0 := 2) (t1 := 0) (k1 := 2) hB hc hcx hcy0 (by decide)
      ⟨by norm_num, by norm_num⟩ (by decide) (by decide),
    brB_zero hq42 105 _ hB hc hcx hcy0 (by norm_num) (fun r hr => by
      simp only [Finset.mem_Icc] at hr
      obtain ⟨h0, h3⟩ := hr
      interval_cases r <;>
      · simp only [sig1, dmon, Msh, mono_mul]
        apply mono_add_zero
        · norm_num [eTn, eAT, c2]
        · unfold cTn cAT; zsimp; exact Z_mod (by first | omega | (ring_nf; omega)))]
  simp

/-- zeros of `j(B_2)` with `ℓ = 2`. -/
theorem zB6 (j : ℤ) : ev F0 (1401) (Z84 ^ (3 + 12 * j)) = 0 := by
  have hcx : Z84 ^ (3 + 12 * j) ≠ 0 := zpow_ne_zero _ Z_ne
  have hB : eBT (qe := 42) 105 2 (1401) = 160 * ((42 : ℕ) : ℤ) * 2 := by norm_num [eBT]
  have hc : cBT (Z84 ^ (63 : ℤ)) (Z84 ^ (3 + 12 * j)) = 1 := by
    unfold cBT; zsimp; exact Z_eq_one (by omega)
  unfold F0
  rw [FS_ev_B hq42 105 _ (s0 := 2) (ℓ0 := 2) (t1 := 2) (k1 := 3) hB hc hcx hcy0 (by decide)
      ⟨by norm_num, by norm_num⟩ (by decide) (by decide),
    brB_zero hq42 105 _ hB hc hcx hcy0 (by norm_num) (fun r hr => by
      simp only [Finset.mem_Icc] at hr
      obtain ⟨h0, h3⟩ := hr
      interval_cases r <;>
      · simp only [sig1, dmon, Msh, mono_mul]
        apply mono_add_zero
        · norm_num [eTn, eAT, c2]
        · unfold cTn cAT; zsimp; exact Z_mod (by first | omega | (ring_nf; omega)))]
  simp

/-- zeros of `j(A_0)` with `ℓ = 0`. -/
theorem zA0 (j : ℤ) : ev F0 (441) (Z84 ^ (7 + 28 * j)) = 0 := by
  have hcx : Z84 ^ (7 + 28 * j) ≠ 0 := zpow_ne_zero _ Z_ne
  have hA : eAT (qe := 42) 105 0 (441) = 160 * ((42 : ℕ) : ℤ) * 0 := by norm_num [eAT]
  have hc : cAT (Z84 ^ (63 : ℤ)) (Z84 ^ (7 + 28 * j)) = 1 := by
    unfold cAT; zsimp; exact Z_eq_one (by omega)
  unfold F0
  rw [FS_ev_A hq42 105 _ (r0 := 0) (ℓ0 := 0) (t1 := 2) (k1 := 1) hA hc hcx hcy0 (by decide)
      ⟨by norm_num, by norm_num⟩ (by decide) (by decide),
    brA_zero hq42 105 _ hA hc hcx hcy0 (by norm_num) (fun s hs => by
      simp only [Finset.mem_Icc] at hs
      obtain ⟨h0, h3⟩ := hs
      interval_cases s <;>
      · simp only [SA, sig2, dmon, Msh, mono_mul]
        apply mono_add_zero
        · norm_num [eTn, eBT, c2]
        · unfold cTn cBT; zsimp; exact Z_mod (by first | omega | (ring_nf; omega)))]
  simp

/-- zeros of `j(A_1)` with `ℓ = 0`. -/
theorem zA1 (j : ℤ) : ev F0 (1001) (Z84 ^ (7 + 28 * j)) = 0 := by
  have hcx : Z84 ^ (7 + 28 * j) ≠ 0 := zpow_ne_zero _ Z_ne
  have hA : eAT (qe := 42) 105 1 (1001) = 160 * ((42 : ℕ) : ℤ) * 0 := by norm_num [eAT]
  have hc : cAT (Z84 ^ (63 : ℤ)) (Z84 ^ (7 + 28 * j)) = 1 := by
    unfold cAT; zsimp; exact Z_eq_one (by omega)
  unfold F0
  rw [FS_ev_A hq42 105 _ (r0 := 1) (ℓ0 := 0) (t1 := 0) (k1 := 0) hA hc hcx hcy0 (by decide)
      ⟨by norm_num, by norm_num⟩ (by decide) (by decide),
    brA_zero hq42 105 _ hA hc hcx hcy0 (by norm_num) (fun s hs => by
      simp only [Finset.mem_Icc] at hs
      obtain ⟨h0, h3⟩ := hs
      interval_cases s <;>
      · simp only [SA, sig2, dmon, Msh, mono_mul]
        apply mono_add_zero
        · norm_num [eTn, eBT, c2]
        · unfold cTn cBT; zsimp; exact Z_mod (by first | omega | (ring_nf; omega)))]
  simp

/-- zeros of `j(A_2)` with `ℓ = 0`. -/
theorem zA2 (j : ℤ) : ev F0 (1561) (Z84 ^ (7 + 28 * j)) = 0 := by
  have hcx : Z84 ^ (7 + 28 * j) ≠ 0 := zpow_ne_zero _ Z_ne
  have hA : eAT (qe := 42) 105 2 (1561) = 160 * ((42 : ℕ) : ℤ) * 0 := by norm_num [eAT]
  have hc : cAT (Z84 ^ (63 : ℤ)) (Z84 ^ (7 + 28 * j)) = 1 := by
    unfold cAT; zsimp; exact Z_eq_one (by omega)
  unfold F0
  rw [FS_ev_A hq42 105 _ (r0 := 2) (ℓ0 := 0) (t1 := 1) (k1 := 0) hA hc hcx hcy0 (by decide)
      ⟨by norm_num, by norm_num⟩ (by decide) (by decide),
    brA_zero hq42 105 _ hA hc hcx hcy0 (by norm_num) (fun s hs => by
      simp only [Finset.mem_Icc] at hs
      obtain ⟨h0, h3⟩ := hs
      interval_cases s <;>
      · simp only [SA, sig2, dmon, Msh, mono_mul]
        apply mono_add_zero
        · norm_num [eTn, eBT, c2]
        · unfold cTn cBT; zsimp; exact Z_mod (by first | omega | (ring_nf; omega)))]
  simp

/-! ## The 56 zeros -/

def peT : Fin 56 → ℤ := ![-39, -39, -39, -39, -39, -39, -39, 201, 201, 201, 201, 201, 201, 201, 441, 441, 441, 441, 441, 441, 441, 681, 681, 681, 681, 681, 681, 681, 921, 921, 921, 921, 921, 921, 921, 1161, 1161, 1161, 1161, 1161, 1161, 1161, 1401, 1401, 1401, 1401, 1401, 1401, 1401, 1001, 1001, 1001, 1561, 1561, 1561, 441]
def pmT : Fin 56 → ℤ := ![3 + 12 * 0, 3 + 12 * 1, 3 + 12 * 2, 3 + 12 * 3, 3 + 12 * 4, 3 + 12 * 5, 3 + 12 * 6, 3 + 12 * 0, 3 + 12 * 1, 3 + 12 * 2, 3 + 12 * 3, 3 + 12 * 4, 3 + 12 * 5, 3 + 12 * 6, 3 + 12 * 0, 3 + 12 * 1, 3 + 12 * 2, 3 + 12 * 3, 3 + 12 * 4, 3 + 12 * 5, 3 + 12 * 6, 3 + 12 * 0, 3 + 12 * 1, 3 + 12 * 2, 3 + 12 * 3, 3 + 12 * 4, 3 + 12 * 5, 3 + 12 * 6, 3 + 12 * 0, 3 + 12 * 1, 3 + 12 * 2, 3 + 12 * 3, 3 + 12 * 4, 3 + 12 * 5, 3 + 12 * 6, 3 + 12 * 0, 3 + 12 * 1, 3 + 12 * 2, 3 + 12 * 3, 3 + 12 * 4, 3 + 12 * 5, 3 + 12 * 6, 3 + 12 * 0, 3 + 12 * 1, 3 + 12 * 2, 3 + 12 * 3, 3 + 12 * 4, 3 + 12 * 5, 3 + 12 * 6, 7 + 28 * 0, 7 + 28 * 1, 7 + 28 * 2, 7 + 28 * 0, 7 + 28 * 1, 7 + 28 * 2, 7 + 28 * 0]
noncomputable def pcT (i : Fin 56) : ℂ := Z84 ^ pmT i

lemma zeros56 (i : Fin 56) : ev F0 (peT i) (pcT i) = 0 := by
  fin_cases i
  · exact zB0 0
  · exact zB0 1
  · exact zB0 2
  · exact zB0 3
  · exact zB0 4
  · exact zB0 5
  · exact zB0 6
  · exact zB1 0
  · exact zB1 1
  · exact zB1 2
  · exact zB1 3
  · exact zB1 4
  · exact zB1 5
  · exact zB1 6
  · exact zB2 0
  · exact zB2 1
  · exact zB2 2
  · exact zB2 3
  · exact zB2 4
  · exact zB2 5
  · exact zB2 6
  · exact zB3 0
  · exact zB3 1
  · exact zB3 2
  · exact zB3 3
  · exact zB3 4
  · exact zB3 5
  · exact zB3 6
  · exact zB4 0
  · exact zB4 1
  · exact zB4 2
  · exact zB4 3
  · exact zB4 4
  · exact zB4 5
  · exact zB4 6
  · exact zB5 0
  · exact zB5 1
  · exact zB5 2
  · exact zB5 3
  · exact zB5 4
  · exact zB5 5
  · exact zB5 6
  · exact zB6 0
  · exact zB6 1
  · exact zB6 2
  · exact zB6 3
  · exact zB6 4
  · exact zB6 5
  · exact zB6 6
  · exact zA1 0
  · exact zA1 1
  · exact zA1 2
  · exact zA2 0
  · exact zA2 1
  · exact zA2 2
  · exact zA0 0

lemma dist56 : ∀ i j : Fin 56, i ≠ j → (peT i - peT j) % 1680 = 0 → (pmT i - pmT j) % 84 ≠ 0 := by decide

/-- **`F = 0`**. -/
theorem F0_eq_zero : F0 = 0 := by
  have hn : ‖Z84 ^ (63 : ℤ)‖ = 1 := by rw [norm_zpow, Z_norm, one_zpow]
  exact zero_count (NQ := 40 * 42) (by norm_num) 55 (zpow_ne_zero _ hcy0) (FS_mem_Th hq42 105 _ hn) peT pcT
    (fun i => zpow_ne_zero _ Z_ne)
    (fun i j hij a ha => Z_ne_Z (dist56 i j hij (by rw [ha]; push_cast; omega)))
    zeros56

lemma cgood_xstar : CGood (Z84 ^ (63 : ℤ)) (Z84 ^ (21 : ℤ)) := by
  refine ⟨zpow_ne_zero _ Z_ne, ?_, ?_, ?_, ?_⟩
  · unfold cX; zsimp; exact Z_ne_one (by omega)
  · unfold cY; zsimp; exact Z_ne_one (by omega)
  · unfold cAT; zsimp; exact Z_ne_one (by omega)
  · unfold cBT; zsimp; exact Z_ne_one (by omega)

/-- **`D(x*, y*) = 0`**. -/
theorem Dv_xstar : Dv hq42 105 (Z84 ^ (63 : ℤ)) 105 (Z84 ^ (21 : ℤ)) = 0 := by
  have h := FS_ev hq42 105 _ 105 hcy0 cgood_xstar
  have h0 : ev F0 105 (Z84 ^ (21 : ℤ)) = 0 := by
    rw [F0_eq_zero]; exact ev_zero 105 _
  unfold F0 at h0
  rw [h0] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (Pv_ne hq42 105 _ hcy0 cgood_xstar 105)

/-- **HM Theorem 0.3 for `f_{3,7,3}` at `(x*, y*)`**: `J̄ f = J̄ g + J_{160}³ Σ_{r,s} T(r,s)`. -/
theorem hm03_xstar :
    Jb hq42 * ev (fS hq42 105 (Z84 ^ (63 : ℤ))) 105 (Z84 ^ (21 : ℤ)) =
      gNum hq42 105 (Z84 ^ (63 : ℤ)) 105 (Z84 ^ (21 : ℤ)) +
        kap (h160 hq42) * thV hq42 105 (Z84 ^ (63 : ℤ)) 105 (Z84 ^ (21 : ℤ)) := by
  have := Dv_xstar
  unfold Dv at this
  linear_combination this

end MTC
