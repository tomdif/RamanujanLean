import RamanujanTau.BWSharpAll.DetCriterion
import RamanujanTau.BWSharpAll.Growth
import RamanujanTau.BWSharpAll.RowsDet
import RamanujanTau.TheoremA.BWDictionary

/-!
# `b_ℓ(m) → ∞` for every prime `ℓ ≥ 13`

The odd-chain series `L(1), L(3), L(5), …` are linearly independent over `ℚ`:
by `BoylanWebb.L_eq_partition`, `L(2b+1)` is a unit times `Σₙ p(ℓ^{2b+1} n − e) qⁿ`, and
a rational relation would contradict `p(αn)/p(βn) → ∞` (Hardy–Ramanujan) for its top
term. Any `R+1` of them therefore have a nonzero integer coefficient minor `D`, and the
uniform determinant criterion `lt_bEll_of_int_det` gives `b_ℓ(m) > 2k+1` as soon as
`ℓ^m ∤ D`. Hence `b_ℓ(m) → ∞` (`tendsto_bEll`).

This is unconditional and uniform in `ℓ`, but only qualitative: it gives no explicit rate,
far from the conjectured `b_ℓ(m) = 2m − 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanTau.BWSharpAll
open PowerSeries BoylanWebb BLBound Filter

noncomputable section

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- `p(n)` as a real number. -/
abbrev pr (n : ℕ) : ℝ := (Fintype.card (Nat.Partition n) : ℝ)

lemma pZ_of_nonneg {x : ℤ} (hx : 0 ≤ x) : pZ x = (Fintype.card (Nat.Partition x.toNat) : ℤ) := by
  rw [pZ, if_neg (not_lt.mpr hx), MockTheta5.JTP.coeff_partitionGF_eq_card]

lemma pZ_le_pr (x : ℤ) (N : ℕ) (h : x ≤ N) : ((pZ x : ℤ) : ℝ) ≤ pr N := by
  by_cases hx : x < 0
  · rw [pZ, if_pos hx]; simp [pr]
  · rw [pZ_of_nonneg (not_lt.mp hx)]
    push_cast
    exact_mod_cast card_partition_mono (show x.toNat ≤ N by omega)

lemma pr_le_pZ (x : ℤ) (N : ℕ) (h : (N : ℤ) ≤ x) : pr N ≤ ((pZ x : ℤ) : ℝ) := by
  rw [pZ_of_nonneg (by omega)]
  push_cast
  exact_mod_cast card_partition_mono (show N ≤ x.toNat by omega)

lemma pZ_nonneg' (x : ℤ) : (0 : ℝ) ≤ ((pZ x : ℤ) : ℝ) := by
  by_cases hx : x < 0
  · rw [pZ, if_pos hx]; simp
  · rw [pZ_of_nonneg (not_lt.mp hx)]; positivity

/-- **The partition series `P(2b+1)` along the odd chain are `ℚ`-linearly independent.** -/
theorem pser_linIndep (h13 : 13 ≤ ℓ) (k n : ℕ) :
    LinearIndependent ℚ (fun j : Fin n =>
      PowerSeries.map (Int.castRingHom ℚ) (Pser ℓ (2 * (k + j) + 1))) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  simp only [not_forall] at hne
  set S := Finset.univ.filter fun i : Fin n => g i ≠ 0
  have hS : S.Nonempty := by
    obtain ⟨i, hi⟩ := hne; exact ⟨i, by simp [S, hi]⟩
  set J := S.max' hS
  have hJ : g J ≠ 0 := by
    have := S.max'_mem hS; simpa [S] using this
  have hgt : ∀ i, J < i → g i = 0 := by
    intro i hi
    by_contra h
    have : i ≤ J := S.le_max' i (by simp [S, h])
    exact absurd hi (not_lt.mpr this)
  -- coefficientwise relation
  set x : Fin n → ℕ → ℤ := fun i t => (ℓ : ℤ) ^ (2 * (k + i) + 1) * t - eB ℓ (2 * (k + i) + 1)
  have hrel : ∀ t : ℕ, ∑ i, (g i : ℝ) * ((pZ (x i t) : ℤ) : ℝ) = 0 := by
    intro t
    have h := congrArg (PowerSeries.coeff t) hg
    simp only [map_sum, LinearMap.map_smul, smul_eq_mul, PowerSeries.coeff_map, Pser,
      PowerSeries.coeff_mk, map_zero, eq_intCast] at h
    have h' := congrArg (fun q : ℚ => (q : ℝ)) h
    simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast, Rat.cast_zero] at h'
    simpa [x] using h'
  set bJ := 2 * (k + J) + 1
  set α := ℓ ^ bJ - 1
  set β := ℓ ^ (bJ - 2)
  have hℓ1 : 2 ≤ ℓ := hℓ.out.two_le
  have hβ1 : 1 ≤ β := Nat.one_le_pow _ _ (by omega)
  have hβα : β < α := by
    have h1 : ℓ ^ (bJ - 2) * ℓ ≤ ℓ ^ bJ := by
      rw [← pow_succ]; exact Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : ℓ ^ (bJ - 2) * 13 ≤ ℓ ^ (bJ - 2) * ℓ := Nat.mul_le_mul_left _ h13
    simp only [α, β]; omega
  set C : ℝ := ∑ i, |(g i : ℝ)|
  have hgJ : 0 < |(g J : ℝ)| := by simpa using hJ
  have hratio := (ratio_tendsto_atTop hβ1 hβα).eventually_ge_atTop (C / |(g J : ℝ)| + 1)
  obtain ⟨t, ht, htT⟩ := (hratio.and (eventually_ge_atTop (eB ℓ bJ).toNat)).exists
  have hpβ : 0 < pr (β * t) := by simp only [pr]; exact_mod_cast card_partition_pos _
  -- lower bound on the top term
  have hlow : pr (α * t) ≤ ((pZ (x J t) : ℤ) : ℝ) := by
    apply pr_le_pZ
    have he : 0 ≤ eB ℓ bJ := ek_nonneg ℓ _
    have hα : ((α : ℕ) : ℤ) = (ℓ : ℤ) ^ bJ - 1 := by
      simp only [α]; push_cast [Nat.one_le_pow _ _ (show 0 < ℓ by omega)]; ring
    simp only [x]
    push_cast
    rw [hα]
    have : eB ℓ bJ ≤ (t : ℤ) := by omega
    nlinarith
  -- upper bound on the other terms
  have hup : ∀ i, i ≠ J → |(g i : ℝ) * ((pZ (x i t) : ℤ) : ℝ)| ≤ |(g i : ℝ)| * pr (β * t) := by
    intro i hi
    rcases lt_or_gt_of_ne hi with hlt | hgt'
    · rw [abs_mul, abs_of_nonneg (pZ_nonneg' _)]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply pZ_le_pr
      have he : 0 ≤ eB ℓ (2 * (k + i) + 1) := ek_nonneg ℓ _
      have hb : 2 * (k + i) + 1 ≤ bJ - 2 := by
        have : i.val < J.val := hlt
        simp only [bJ]; omega
      have hpow : (ℓ : ℤ) ^ (2 * (k + i) + 1) ≤ (ℓ : ℤ) ^ (bJ - 2) :=
        pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ ℓ by omega)) hb
      simp only [x, β]
      push_cast
      have ht0 : (0 : ℤ) ≤ t := by positivity
      nlinarith
    · rw [hgt i hgt']; simp
  have hsplit := hrel t
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ J)] at hsplit
  have hbound : |(g J : ℝ)| * pr (α * t) ≤ C * pr (β * t) := by
    calc |(g J : ℝ)| * pr (α * t) ≤ |(g J : ℝ)| * ((pZ (x J t) : ℤ) : ℝ) :=
          mul_le_mul_of_nonneg_left hlow (abs_nonneg _)
      _ = |(g J : ℝ) * ((pZ (x J t) : ℤ) : ℝ)| := by rw [abs_mul, abs_of_nonneg (pZ_nonneg' _)]
      _ = |∑ i ∈ Finset.univ.erase J, (g i : ℝ) * ((pZ (x i t) : ℤ) : ℝ)| := by
          rw [show (g J : ℝ) * ((pZ (x J t) : ℤ) : ℝ) =
            -∑ i ∈ Finset.univ.erase J, (g i : ℝ) * ((pZ (x i t) : ℤ) : ℝ) by linarith, abs_neg]
      _ ≤ ∑ i ∈ Finset.univ.erase J, |(g i : ℝ) * ((pZ (x i t) : ℤ) : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.univ.erase J, |(g i : ℝ)| * pr (β * t) :=
          Finset.sum_le_sum fun i hi => hup i (Finset.ne_of_mem_erase hi)
      _ ≤ C * pr (β * t) := by
          rw [← Finset.sum_mul]
          apply mul_le_mul_of_nonneg_right _ hpβ.le
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            fun _ _ _ => abs_nonneg _
  have hr : C / |(g J : ℝ)| + 1 ≤ pr (α * t) / pr (β * t) := ht
  rw [le_div_iff₀ hpβ] at hr
  have : C * pr (β * t) < |(g J : ℝ)| * pr (α * t) := by
    have h1 : (C / |(g J : ℝ)| + 1) * pr (β * t) * |(g J : ℝ)| ≤ pr (α * t) * |(g J : ℝ)| :=
      mul_le_mul_of_nonneg_right hr hgJ.le
    have h2 : (C / |(g J : ℝ)| + 1) * pr (β * t) * |(g J : ℝ)| =
        C * pr (β * t) + |(g J : ℝ)| * pr (β * t) := by field_simp
    nlinarith
  linarith

/-- **The odd-chain series `L(2k+1), L(2k+3), …` are `ℚ`-linearly independent.** -/
theorem L_linIndep (h13 : 13 ≤ ℓ) (k n : ℕ) :
    LinearIndependent ℚ (fun j : Fin n =>
      PowerSeries.map (Int.castRingHom ℚ) (L ℓ (2 * (k + j) + 1))) := by
  have h24 := TheoremA.HalfIntegral.h24 (ℓ := ℓ) h13
  set u := PowerSeries.map (Int.castRingHom ℚ) (RankProof.Ea ℓ (hℓ0 ℓ) MockTheta5.JTP.qfacInf)
  have hu : IsUnit u := (MockTheta5.JTP.isUnit_qfacInf.map (RankProof.Ea ℓ (hℓ0 ℓ))).map _
  have hfam : (fun j : Fin n => PowerSeries.map (Int.castRingHom ℚ) (L ℓ (2 * (k + j) + 1))) =
      (LinearMap.mulLeft ℚ u) ∘ (fun j : Fin n =>
        PowerSeries.map (Int.castRingHom ℚ) (Pser ℓ (2 * (k + j) + 1))) := by
    funext j
    simp only [Function.comp_apply, LinearMap.mulLeft_apply, u]
    rw [(L_eq_partition ℓ h24 (k + j)).2, map_mul]
  rw [hfam]
  apply (pser_linIndep h13 k n).map'
  rw [LinearMap.ker_eq_bot]
  intro a b hab
  exact hu.mul_left_cancel hab

/-- **For every tail `2k+1`, eventually `b_ℓ(m) > 2k+1`.** -/
theorem lt_bEll_eventually (h13 : 13 ≤ ℓ) (k : ℕ) : ∃ m₀, ∀ m ≥ m₀, 2 * k + 1 < bEll ℓ m := by
  set n := (ℓ + 12) / 24 + 1
  obtain ⟨rows, hrows⟩ := exists_rows_det_ne_zero _ (L_linIndep (ℓ := ℓ) h13 k n)
  set M : Matrix (Fin n) (Fin n) ℤ := fun i j => coeff (rows i) (L ℓ (2 * (k + j) + 1))
  have hD : M.det ≠ 0 := by
    intro h0
    apply hrows
    have : (fun i j => coeff (rows i) (PowerSeries.map (Int.castRingHom ℚ)
        (L ℓ (2 * (k + (j : Fin n)) + 1)))) = (Int.castRingHom ℚ).mapMatrix M := by
      ext i j; simp [M, PowerSeries.coeff_map]
    rw [this, ← RingHom.map_det, h0, map_zero]
  refine ⟨M.det.natAbs + 1, fun m hm => ?_⟩
  apply lt_bEll_of_int_det h13 m (by omega) k (fun j => j) rows
  intro hdvd
  change (ℓ : ℤ) ^ m ∣ M.det at hdvd
  have hle := Int.le_of_dvd (by positivity) ((Int.dvd_natAbs).mpr hdvd)
  have hlt : (M.det.natAbs : ℤ) < (ℓ : ℤ) ^ m := by
    have h1 : M.det.natAbs < 2 ^ m := by
      have := Nat.lt_two_pow_self (n := m); omega
    have h2 : 2 ^ m ≤ ℓ ^ m := Nat.pow_le_pow_left hℓ.out.two_le m
    exact_mod_cast (show M.det.natAbs < ℓ ^ m by omega)
  linarith

/-- **`b_ℓ(m) → ∞` for every prime `ℓ ≥ 13`.** -/
theorem tendsto_bEll (h13 : 13 ≤ ℓ) : Tendsto (bEll ℓ) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro B
  obtain ⟨m₀, hm₀⟩ := lt_bEll_eventually h13 B
  exact ⟨m₀, fun m hm => by have := hm₀ m hm; omega⟩

end

end RamanujanTau.BWSharpAll
