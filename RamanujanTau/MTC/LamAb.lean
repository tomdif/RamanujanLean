/-
# The Lambert numerator equals the library's Appell–Lerch sum

For `x z` in the window `−N < val(xz) < N`, the Lambert form `A(x, z) = Σ_r (−1)^r q^{C(r,2)} z^r/(1 − q^{r−1}xz)`
(`Alam`) agrees with `ALz.Ab` (`A_{r≠1}` expanded geometrically on the cones, minus the `r = 1` term): each row
`r ≥ 2` of `ALz.asF2` is the geometric series of `(1 − q^{r−1}xz)⁻¹`, each row `r ≤ 0` the geometric series in
`(q^{r−1}xz)⁻¹`, and the row `r = 1` is empty. This makes `ALz.change_of_z2` and `ALz.kappa_eq_jacobi` available for
`Alam` / `Av`.
-/
import RamanujanTau.MTC.Lambert
import RamanujanTau.ALExt

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset

lemma hs_fin {ι : Type*} {s : SummableFamily ℤ ℂ ι} (S : Finset ι) (h : ∀ i ∉ S, s i = 0) :
    hs s = ∑ i ∈ S, s i := by
  ext g
  rw [hs, SummableFamily.coeff_hsum_eq_sum_of_subset (t := S) (fun i hi => by
    by_contra hS; apply hi; rw [h i hS, HahnSeries.coeff_zero]), HahnSeries.coeff_sum]

lemma mono_ext_b {E E' : ℤ} {C C' : ℂ} (hE : E = E') (hC : C = C') : (mono E C : L) = mono E' C' := by
  subst hE hC; rfl

lemma inv_eq_hs_geoP (e : ℤ) (c : ℂ) (he : 0 < e) : ((1 : L) - mono e c)⁻¹ = hs (geoP e c he) :=
  inv_eq_of_mul_eq_one_right (hs_geoP e c he)

section Bridge
variable {N : ℕ} (hN : 1 ≤ N)

include hN in
lemma row_asF2_pos {a β : ℤ} (hlo : -N < a + β) (hhi : a + β < N) (cx cp : ℂ) (r : ℤ) (hr : 2 ≤ r) :
    hs (row (asF2 hN hlo hhi cx cp) r) =
      mono (N * c2 r + β * r) ((-1) ^ r * cp ^ r) * (1 - mono (N * (r - 1) + a + β) (cx * cp))⁻¹ := by
  have hE : 0 < (N : ℤ) * (r - 1) + a + β := by
    have : (N : ℤ) ≤ N * (r - 1) := le_mul_of_one_le_right (by positivity) (by omega)
    omega
  rw [inv_eq_hs_geoP _ _ hE]
  refine hsum_reindex _ _ (Equiv.refl ℤ) _ fun j => ?_
  rw [Equiv.refl_apply, row_apply, asF2_apply hN hlo hhi, geoP_apply]
  simp only
  by_cases hj : 0 ≤ j
  · rw [if_pos (show cone2 r j from ⟨Or.inl ⟨by omega, hj⟩, by omega⟩), if_pos hj, mono_mul, sgnC,
      if_pos (by omega)]
    exact mono_ext_b (by unfold asExp; ring) (by ring)
  · rw [if_neg (show ¬ cone2 r j from fun h => by rcases h.1 with h1 | h1 <;> omega), if_neg hj, mul_zero]

include hN in
lemma row_asF2_neg {a β : ℤ} (hlo : -N < a + β) (hhi : a + β < N) {cx cp : ℂ} (hx : cx ≠ 0) (hp : cp ≠ 0)
    (r : ℤ) (hr : r ≤ 0) :
    hs (row (asF2 hN hlo hhi cx cp) r) =
      mono (N * c2 r + β * r) ((-1) ^ r * cp ^ r) * (1 - mono (N * (r - 1) + a + β) (cx * cp))⁻¹ := by
  have hE : 0 < -((N : ℤ) * (r - 1) + a + β) := by
    have : (N : ℤ) * (r - 1) ≤ -N := by nlinarith
    omega
  have hc : cx * cp ≠ 0 := mul_ne_zero hx hp
  have h := hsum_reindex (geoP _ (cx * cp)⁻¹ hE) (row (asF2 hN hlo hhi cx cp) r) (Equiv.subLeft (-1))
    (mono (N * c2 r + β * r - ((N : ℤ) * (r - 1) + a + β)) (-((-1) ^ r * cp ^ r) * (cx * cp)⁻¹)) fun i => by
      rw [Equiv.subLeft_apply, row_apply, asF2_apply hN hlo hhi, geoP_apply]
      simp only
      by_cases hi : 0 ≤ i
      · rw [if_pos (show cone2 r (-1 - i) from ⟨Or.inr ⟨hr, by omega⟩, by omega⟩), if_pos hi, mono_mul, sgnC,
          if_neg (by omega)]
        refine mono_ext_b (by unfold asExp; ring) ?_
        have e : (cx * cp) ^ (-1 - i) = (cx * cp)⁻¹ * ((cx * cp)⁻¹) ^ i := by
          rw [inv_zpow, ← zpow_neg, ← zpow_neg_one, ← zpow_add₀ hc]; first | done | ring_nf
        rw [e]; ring
      · rw [if_neg (show ¬ cone2 r (-1 - i) from fun h => by rcases h.1 with h1 | h1 <;> omega), if_neg hi,
          mul_zero]
  rw [h, ← inv_eq_hs_geoP]
  set E : ℤ := (N : ℤ) * (r - 1) + a + β
  have hw : (mono (-E) (cx * cp)⁻¹ : L) = (mono E (cx * cp))⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [mono_mul, show (1 : L) = mono 0 1 from rfl]
    exact mono_ext_b (by ring) (inv_mul_cancel₀ hc)
  have hsplit : (mono (N * c2 r + β * r - E) (-((-1) ^ r * cp ^ r) * (cx * cp)⁻¹) : L) =
      -(mono (N * c2 r + β * r) ((-1) ^ r * cp ^ r) * mono (-E) (cx * cp)⁻¹) := by
    rw [mono_mul, show -(mono (N * c2 r + β * r + -E) ((-1) ^ r * cp ^ r * (cx * cp)⁻¹) : L) =
      mono (N * c2 r + β * r + -E) (-((-1) ^ r * cp ^ r * (cx * cp)⁻¹)) by simp [mono]]
    exact mono_ext_b (by ring) (by ring)
  rw [hsplit, hw]
  have h0 : (mono E (cx * cp) : L) ≠ 0 := by simp [mono, hc]
  have h1 : (1 : L) - mono E (cx * cp) ≠ 0 := one_sub_mono_ne_zero fun h => absurd h.1 (by omega)
  have h2 : (mono E (cx * cp) : L) - 1 ≠ 0 := fun h => h1 (by linear_combination -h)
  field_simp
  ring

include hN in
lemma row_asF2_one {a β : ℤ} (hlo : -N < a + β) (hhi : a + β < N) (cx cp : ℂ) :
    hs (row (asF2 hN hlo hhi cx cp) 1) = 0 := by
  rw [hs_fin ∅ fun j _ => by
    rw [row_apply, asF2_apply hN hlo hhi]; simp only; rw [if_neg fun h => h.2 rfl]]
  simp

/-- **`Alam = Ab`** in the window `−N < val(xz) < N`. -/
theorem Alam_eq_Ab {ex : ℤ} {cx : ℂ} {ez : ℤ} {cz : ℂ} (hx : cx ≠ 0) (hz : cz ≠ 0) (hok : LamOK N ex cx ez cz)
    (hlo : -N < ex + ez) (hhi : ex + ez < N) : Alam hN hx hz hok = ALz.Ab hN hlo hhi cx cz := by
  have hrow : ∀ r : ℤ, r ≠ 1 → rowFam (asF2 hN hlo hhi cx cz) r = lamT N ex cx ez cz r := fun r hr => by
    rw [rowFam_apply]
    rcases le_or_gt r 0 with h | h
    · rw [row_asF2_neg hN hlo hhi hx hz r h]; rfl
    · rw [row_asF2_pos hN hlo hhi cx cz r (by omega)]; rfl
  have hD : hs (lamF hN hx hz hok) - hs (rowFam (asF2 hN hlo hhi cx cz)) = lamT N ex cx ez cz 1 := by
    rw [hs, hs, ← SummableFamily.hsum_sub, ← hs]
    rw [hs_fin {1} fun i hi => by
      rw [SummableFamily.sub_apply, hrow i (by simpa using hi)]
      exact sub_self _]
    rw [Finset.sum_singleton, SummableFamily.sub_apply, rowFam_apply, row_asF2_one, sub_zero]
    rfl
  have h1 : lamT N ex cx ez cz 1 = -(mono ez cz * (1 - mono (ex + ez) (cx * cz))⁻¹) := by
    unfold lamT wE
    rw [show (N : ℤ) * c2 1 + ez * 1 = ez by norm_num [c2], show (N : ℤ) * (1 - 1) + ex + ez = ex + ez by ring,
      zpow_one, zpow_one, neg_one_mul, show (mono ez (-cz) : L) = -mono ez cz by simp [mono]]
    ring
  unfold Alam ALz.Ab Aser2
  rw [← hs_rowFam]
  linear_combination hD + h1

end Bridge

end MTC
