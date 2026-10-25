/-
# HM Theorem 0.3 for `f_{1,4,1}` at the `ψ₀` point

`q = t⁸`, `y* = i t^{12} = W⁴ t^{12}`, `x* = −i t⁴ = W^{12} t⁴` (`W = e^{πi/8}`). `F` vanishes at the 16 zeros of
the `j(B_s)` (`x = W^{3+4j} t^{ex}`, `ex ∈ {−9, 21, 51, 81}`) and at the zero `x = −t^{96}` of `j(A_0)` (the residue
identities `brB_zero`, `brA_zero`); these 17 points are pairwise inequivalent under `x ↦ q^{15}x`, and `F ∈ Th(16)`,
so `F = 0` (`FP_eq_zero`), whence `hm03_psi`.
-/
import RamanujanTau.MTC.Ev141
import RamanujanTau.MTC.Z16
import RamanujanTau.MTC.Zeros373

set_option autoImplicit false

namespace MTC.H141
open ALz HahnSeries Finset MTC

lemma Pv_ne {qe : ℕ} (hqe : 1 ≤ qe) (ey : ℤ) (cy : ℂ) (hcy : cy ≠ 0) {cx : ℂ} (h : CGood cy cx) (ex : ℤ) :
    Pv hqe ey cy ex cx ≠ 0 := by
  unfold Pv
  refine mul_ne_zero (List.prod_ne_zero ?_) (List.prod_ne_zero ?_) <;>
    simp only [List.mem_map, not_exists, not_and] <;> intro r _ h0
  · exact θ_ne_zero (h45 hqe) (cAT_ne cy h.1 hcy) (fun _ _ => h.2.2.2.1) h0
  · exact θ_ne_zero (h45 hqe) (cBT_ne cy h.1 hcy) (fun _ _ => h.2.2.2.2) h0

lemma hq8 : 1 ≤ 8 := by norm_num

/-- the auxiliary series at `y*`. -/
noncomputable abbrev FP : ℤ → L := FS hq8 12 (W16 ^ (4 : ℤ))

lemma hcyP : W16 ^ (4 : ℤ) ≠ 0 := zpow_ne_zero _ W_ne

theorem zB0 (j : ℤ) : ev FP (-9) (W16 ^ (3 + 4 * j)) = 0 := by
  have hcx : W16 ^ (3 + 4 * j) ≠ 0 := zpow_ne_zero _ W_ne
  have hB : eBT (qe := 8) 12 0 (-9) = 45 * ((8 : ℕ) : ℤ) * 0 := by norm_num [eBT]
  have hc : cBT (W16 ^ (4 : ℤ)) (W16 ^ (3 + 4 * j)) = 1 := by
    unfold cBT; wsimp; exact W_eq_one (by omega)
  unfold FP
  rw [FS_ev_B hq8 12 _ (s0 := 0) (ℓ0 := 0) (k1 := 0) hB hc hcx hcyP (by decide) (by decide) (by decide),
    brB_zero hq8 12 _ hB hc hcx hcyP (fun r hr => by
      simp only [Finset.mem_Icc] at hr
      obtain ⟨h0, h3⟩ := hr
      interval_cases r <;>
      · simp only [sig1, dmon, Msh, mono_mul]
        apply mono_add_zero
        · norm_num [eTn, eAT, c2]
        · unfold cTn cAT; wsimp; exact W_mod (by first | omega | (ring_nf; omega)))]
  simp

theorem zB1 (j : ℤ) : ev FP (51) (W16 ^ (3 + 4 * j)) = 0 := by
  have hcx : W16 ^ (3 + 4 * j) ≠ 0 := zpow_ne_zero _ W_ne
  have hB : eBT (qe := 8) 12 1 (51) = 45 * ((8 : ℕ) : ℤ) * 1 := by norm_num [eBT]
  have hc : cBT (W16 ^ (4 : ℤ)) (W16 ^ (3 + 4 * j)) = 1 := by
    unfold cBT; wsimp; exact W_eq_one (by omega)
  unfold FP
  rw [FS_ev_B hq8 12 _ (s0 := 1) (ℓ0 := 1) (k1 := 2) hB hc hcx hcyP (by decide) (by decide) (by decide),
    brB_zero hq8 12 _ hB hc hcx hcyP (fun r hr => by
      simp only [Finset.mem_Icc] at hr
      obtain ⟨h0, h3⟩ := hr
      interval_cases r <;>
      · simp only [sig1, dmon, Msh, mono_mul]
        apply mono_add_zero
        · norm_num [eTn, eAT, c2]
        · unfold cTn cAT; wsimp; exact W_mod (by first | omega | (ring_nf; omega)))]
  simp

theorem zB2 (j : ℤ) : ev FP (21) (W16 ^ (3 + 4 * j)) = 0 := by
  have hcx : W16 ^ (3 + 4 * j) ≠ 0 := zpow_ne_zero _ W_ne
  have hB : eBT (qe := 8) 12 2 (21) = 45 * ((8 : ℕ) : ℤ) * 1 := by norm_num [eBT]
  have hc : cBT (W16 ^ (4 : ℤ)) (W16 ^ (3 + 4 * j)) = 1 := by
    unfold cBT; wsimp; exact W_eq_one (by omega)
  unfold FP
  rw [FS_ev_B hq8 12 _ (s0 := 2) (ℓ0 := 1) (k1 := 1) hB hc hcx hcyP (by decide) (by decide) (by decide),
    brB_zero hq8 12 _ hB hc hcx hcyP (fun r hr => by
      simp only [Finset.mem_Icc] at hr
      obtain ⟨h0, h3⟩ := hr
      interval_cases r <;>
      · simp only [sig1, dmon, Msh, mono_mul]
        apply mono_add_zero
        · norm_num [eTn, eAT, c2]
        · unfold cTn cAT; wsimp; exact W_mod (by first | omega | (ring_nf; omega)))]
  simp

theorem zB3 (j : ℤ) : ev FP (81) (W16 ^ (3 + 4 * j)) = 0 := by
  have hcx : W16 ^ (3 + 4 * j) ≠ 0 := zpow_ne_zero _ W_ne
  have hB : eBT (qe := 8) 12 0 (81) = 45 * ((8 : ℕ) : ℤ) * 1 := by norm_num [eBT]
  have hc : cBT (W16 ^ (4 : ℤ)) (W16 ^ (3 + 4 * j)) = 1 := by
    unfold cBT; wsimp; exact W_eq_one (by omega)
  unfold FP
  rw [FS_ev_B hq8 12 _ (s0 := 0) (ℓ0 := 1) (k1 := 3) hB hc hcx hcyP (by decide) (by decide) (by decide),
    brB_zero hq8 12 _ hB hc hcx hcyP (fun r hr => by
      simp only [Finset.mem_Icc] at hr
      obtain ⟨h0, h3⟩ := hr
      interval_cases r <;>
      · simp only [sig1, dmon, Msh, mono_mul]
        apply mono_add_zero
        · norm_num [eTn, eAT, c2]
        · unfold cTn cAT; wsimp; exact W_mod (by first | omega | (ring_nf; omega)))]
  simp

theorem zA0 : ev FP 96 (W16 ^ (8 : ℤ)) = 0 := by
  have hcx : W16 ^ (8 : ℤ) ≠ 0 := zpow_ne_zero _ W_ne
  have hA : eAT (qe := 8) 12 0 96 = 45 * ((8 : ℕ) : ℤ) * 0 := by norm_num [eAT]
  have hc : cAT (W16 ^ (4 : ℤ)) (W16 ^ (8 : ℤ)) = 1 := by
    unfold cAT; wsimp; exact W_eq_one (by omega)
  unfold FP
  rw [FS_ev_A hq8 12 _ (r0 := 0) (ℓ0 := 0) (k1 := 0) hA hc hcx hcyP (by decide) (by decide) (by decide),
    brA_zero hq8 12 _ hA hc hcx hcyP (fun s hs => by
      simp only [Finset.mem_Icc] at hs
      obtain ⟨h0, h3⟩ := hs
      interval_cases s <;>
      · simp only [SA, sig1, dmon, Msh, mono_mul]
        apply mono_add_zero
        · norm_num [eTn, eBT, c2]
        · unfold cTn cBT; wsimp; exact W_mod (by first | omega | (ring_nf; omega)))]
  simp

def peT : Fin 17 → ℤ := ![-9, -9, -9, -9, 51, 51, 51, 51, 21, 21, 21, 21, 81, 81, 81, 81, 96]
def pmT : Fin 17 → ℤ := ![3 + 4 * 0, 3 + 4 * 1, 3 + 4 * 2, 3 + 4 * 3, 3 + 4 * 0, 3 + 4 * 1, 3 + 4 * 2, 3 + 4 * 3, 3 + 4 * 0, 3 + 4 * 1, 3 + 4 * 2, 3 + 4 * 3, 3 + 4 * 0, 3 + 4 * 1, 3 + 4 * 2, 3 + 4 * 3, 8]
noncomputable def pcT (i : Fin 17) : ℂ := W16 ^ pmT i

lemma zeros17 (i : Fin 17) : ev FP (peT i) (pcT i) = 0 := by
  fin_cases i
  · exact zB0 0
  · exact zB0 1
  · exact zB0 2
  · exact zB0 3
  · exact zB1 0
  · exact zB1 1
  · exact zB1 2
  · exact zB1 3
  · exact zB2 0
  · exact zB2 1
  · exact zB2 2
  · exact zB2 3
  · exact zB3 0
  · exact zB3 1
  · exact zB3 2
  · exact zB3 3
  · exact zA0

lemma dist17 : ∀ i j : Fin 17, i ≠ j → (peT i - peT j) % 120 = 0 → (pmT i - pmT j) % 16 ≠ 0 := by decide

/-- **`F = 0`**. -/
theorem FP_eq_zero : FP = 0 := by
  have hn : ‖W16 ^ (4 : ℤ)‖ = 1 := by rw [norm_zpow, W_norm, one_zpow]
  exact zero_count (NQ := 15 * 8) (by norm_num) 16 (neg_ne_zero.mpr (zpow_ne_zero _ hcyP)) (FS_mem_Th hq8 12 _ hn)
    peT pcT (fun i => zpow_ne_zero _ W_ne)
    (fun i j hij a ha => W_ne_W (dist17 i j hij (by rw [ha]; push_cast; omega)))
    zeros17

lemma cgood_psi : CGood (W16 ^ (4 : ℤ)) (W16 ^ (12 : ℤ)) := by
  refine ⟨zpow_ne_zero _ W_ne, ?_, ?_, ?_, ?_⟩
  · unfold cX; wsimp; exact W_ne_one (by omega)
  · unfold cY; wsimp; exact W_ne_one (by omega)
  · unfold cAT; wsimp; exact W_ne_one (by omega)
  · unfold cBT; wsimp; exact W_ne_one (by omega)

/-- **`D(x*, y*) = 0`**. -/
theorem Dv_psi : Dv hq8 12 (W16 ^ (4 : ℤ)) 4 (W16 ^ (12 : ℤ)) = 0 := by
  have h := FS_ev hq8 12 _ 4 hcyP cgood_psi
  have h0 : ev FP 4 (W16 ^ (12 : ℤ)) = 0 := by
    rw [FP_eq_zero]; exact ev_zero 4 _
  unfold FP at h0
  rw [h0] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (Pv_ne hq8 12 _ hcyP cgood_psi 4)

/-- **HM Theorem 0.3 for `f_(1, 4, 1)` at `(x*, y*) = (−i t⁴, i t^12)`, `q = t⁸`**. -/
theorem hm03_psi :
    Jb hq8 * ev (fS hq8 12 (W16 ^ (4 : ℤ))) 4 (W16 ^ (12 : ℤ)) =
      gNum hq8 12 (W16 ^ (4 : ℤ)) 4 (W16 ^ (12 : ℤ)) +
        kap (h45 hq8) * thV hq8 12 (W16 ^ (4 : ℤ)) 4 (W16 ^ (12 : ℤ)) := by
  have := Dv_psi
  unfold Dv at this
  linear_combination this

end MTC.H141
