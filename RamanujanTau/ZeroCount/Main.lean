/-
# Counting the nontrivial zeros of `L(Δ,s)`: `T ≪ N(T) ≪ T log T`

See `docs/ZERO_COUNT.md`.

* `window_count` (`Jensen.lean`): zeros, with multiplicity, in `T < Im ≤ T+1` are `≤ C log(|T|+2)`.
* `zeroSet_finite`, `zeroCount` : `N(a,b) = ∑_{ρ ∈ zeroSet a b} mult ρ`, `N(T) = N(0,T)`.
* `zeroSet_eq_of_nonneg` : for `0 ≤ a`, `zeroSet a b` is *every* zero with `a < Im ≤ b`
  (edge non-vanishing).
* `zeroCount_window` : `N(T+1) − N(T) ≤ C log(T+2)`.
* `zeroCount_le` : `N(T) ≤ C (T+1) log(T+2)` for `T ≥ 0`; `zeroCount_le_T_log_T`.
* `zeroCount_two_sided` : `c T ≤ N(T) ≤ C T log T` for `T ≥ T₀` (lower bound from Hafner).
-/
import RamanujanTau.ZeroCount.Jensen
import RamanujanTau.EdgeNonvanishing.Main
import RamanujanTau.HardyCountHafner.Main

namespace RamanujanTau.ZeroCount

open Complex Set
open RamanujanTau.HeckeL

lemma card_le_sum_mult (S : Finset ℂ) (hS : ∀ u ∈ S, tauL u = 0) : S.card ≤ ∑ u ∈ S, mult u := by
  rw [Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun u hu => one_le_mult (hS u hu)

lemma zeroSet_window_finite (T : ℝ) : (zeroSet T (T + 1)).Finite := by
  obtain ⟨C, _, hC⟩ := window_count
  by_contra h
  obtain ⟨S, hS, hcard⟩ :=
    Set.Infinite.exists_subset_card_eq h (⌈C * Real.log (|T| + 2)⌉₊ + 1)
  have h1 := hC T S hS
  have h2 : S.card ≤ ∑ u ∈ S, mult u := card_le_sum_mult S fun u hu => (hS hu).1
  have h3 : ((S.card : ℕ) : ℝ) ≤ C * Real.log (|T| + 2) :=
    le_trans (by exact_mod_cast h2) h1
  rw [hcard] at h3
  push_cast at h3
  linarith [Nat.le_ceil (C * Real.log (|T| + 2))]

/-- The index of the unit window `a + k < Im ≤ a + k + 1` containing `u`. -/
noncomputable def winIdx (a : ℝ) (u : ℂ) : ℕ := ⌈u.im - a⌉₊ - 1

lemma winIdx_spec {a : ℝ} {u : ℂ} (h : a < u.im) :
    a + (winIdx a u : ℝ) < u.im ∧ u.im ≤ a + (winIdx a u : ℝ) + 1 := by
  have hpos : 0 < ⌈u.im - a⌉₊ := Nat.ceil_pos.mpr (by linarith)
  have he : winIdx a u + 1 = ⌈u.im - a⌉₊ := by unfold winIdx; omega
  have hne : winIdx a u + 1 ≠ 0 := by omega
  have := (Nat.ceil_eq_iff hne).mp he.symm
  push_cast at this
  constructor <;> linarith [this.1, this.2]

lemma winIdx_lt {a b : ℝ} {u : ℂ} (h1 : a < u.im) (h2 : u.im ≤ b) :
    winIdx a u < ⌈b - a⌉₊ := by
  have hpos : 0 < ⌈u.im - a⌉₊ := Nat.ceil_pos.mpr (by linarith)
  have hm : ⌈u.im - a⌉₊ ≤ ⌈b - a⌉₊ := Nat.ceil_mono (by linarith)
  unfold winIdx; omega

/-- Every `zeroSet a b` is finite. -/
theorem zeroSet_finite (a b : ℝ) : (zeroSet a b).Finite := by
  have hsub : zeroSet a b ⊆ ⋃ k ∈ Set.Iio ⌈b - a⌉₊, zeroSet (a + k) (a + k + 1) := by
    intro u hu
    obtain ⟨h0, h1, h2, h3, h4⟩ := hu
    obtain ⟨s1, s2⟩ := winIdx_spec h3
    exact Set.mem_biUnion (x := winIdx a u) (winIdx_lt h3 h4) ⟨h0, h1, h2, s1, s2⟩
  exact ((Set.finite_Iio (⌈b - a⌉₊ : ℕ)).biUnion fun (k : ℕ) _ =>
    zeroSet_window_finite (a + k)).subset hsub

/-- `N(a,b)`: number of zeros of `L(Δ,s)` with `11/2 < Re < 13/2`, `a < Im ≤ b`, counted with
multiplicity. -/
noncomputable def zeroCountAB (a b : ℝ) : ℕ := ∑ u ∈ (zeroSet_finite a b).toFinset, mult u

/-- `N(T) = N(0,T)`. -/
noncomputable def zeroCount (T : ℝ) : ℕ := zeroCountAB 0 T

/-- For `0 ≤ a`, the strip condition is automatic: `zeroSet a b` is the set of *all* zeros of
`L(Δ,s)` with `a < Im ≤ b` (no zeros on `Re ≥ 13/2` or `Re ≤ 11/2` off the real axis). -/
theorem zeroSet_eq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) :
    zeroSet a b = {u : ℂ | tauL u = 0 ∧ a < u.im ∧ u.im ≤ b} := by
  ext u
  constructor
  · rintro ⟨h0, -, -, h3, h4⟩; exact ⟨h0, h3, h4⟩
  · rintro ⟨h0, h3, h4⟩
    have hn : ∀ n : ℕ, u ≠ -n := by
      intro n hu; rw [hu] at h3; simp at h3; linarith
    refine ⟨h0, ?_, ?_, h3, h4⟩
    · by_contra h
      exact EdgeNonvanishing.tauL_ne_zero_of_le (by linarith) hn h0
    · by_contra h
      exact EdgeNonvanishing.tauL_ne_zero_of_ge (by linarith) h0

/-- Additivity `N(a,c) = N(a,b) + N(b,c)` for `a ≤ b ≤ c`. -/
theorem zeroCountAB_add {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    zeroCountAB a c = zeroCountAB a b + zeroCountAB b c := by
  classical
  unfold zeroCountAB
  have hU : (zeroSet_finite a c).toFinset =
      (zeroSet_finite a b).toFinset ∪ (zeroSet_finite b c).toFinset := by
    ext u
    simp only [Finset.mem_union, Set.Finite.mem_toFinset, zeroSet, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h0, h1, h2, h3, h4⟩
      rcases le_or_gt u.im b with h | h
      · exact Or.inl ⟨h0, h1, h2, h3, h⟩
      · exact Or.inr ⟨h0, h1, h2, h, h4⟩
    · rintro (⟨h0, h1, h2, h3, h4⟩ | ⟨h0, h1, h2, h3, h4⟩)
      · exact ⟨h0, h1, h2, h3, by linarith⟩
      · exact ⟨h0, h1, h2, by linarith, h4⟩
  rw [hU, Finset.sum_union]
  rw [Finset.disjoint_left]
  intro u hu hu'
  simp only [Set.Finite.mem_toFinset, zeroSet, Set.mem_setOf_eq] at hu hu'
  linarith [hu.2.2.2.2, hu'.2.2.2.1]

/-- **Zeros in unit windows**: `N(T+1) − N(T) ≤ C log(T+2)` (with multiplicity), uniformly in
real `T` for the window count `N(T, T+1)`. -/
theorem zeroCount_window : ∃ C : ℝ, 0 ≤ C ∧
    (∀ T : ℝ, (zeroCountAB T (T + 1) : ℝ) ≤ C * Real.log (|T| + 2)) ∧
    (∀ T : ℝ, 0 ≤ T → (zeroCount (T + 1) : ℝ) - zeroCount T ≤ C * Real.log (T + 2)) := by
  obtain ⟨C, hC0, hC⟩ := window_count
  have hw : ∀ T : ℝ, (zeroCountAB T (T + 1) : ℝ) ≤ C * Real.log (|T| + 2) := fun T =>
    hC T _ (by intro u hu; exact (Set.Finite.mem_toFinset _).mp hu)
  refine ⟨C, hC0, hw, fun T hT => ?_⟩
  unfold zeroCount
  rw [zeroCountAB_add hT (by linarith : T ≤ T + 1)]
  push_cast
  have := hw T
  rw [abs_of_nonneg hT] at this
  linarith

/-- **Upper bound** `N(T) ≤ C (T+1) log(T+2)` for `T ≥ 0`, in the general form: every finite set
of zeros in the strip with `0 < Im ≤ T`, counted with multiplicity. -/
theorem sum_mult_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T → ∀ S : Finset ℂ,
    (↑S : Set ℂ) ⊆ zeroSet 0 T →
    ((∑ u ∈ S, mult u : ℕ) : ℝ) ≤ C * (T + 1) * Real.log (T + 2) := by
  classical
  obtain ⟨C, hC0, hC⟩ := window_count
  refine ⟨C, hC0, fun T hT S hS => ?_⟩
  set n := ⌈T - 0⌉₊ with hn
  have hmaps : ∀ u ∈ S, winIdx 0 u ∈ Finset.range n := by
    intro u hu
    obtain ⟨_, _, _, h3, h4⟩ := hS hu
    exact Finset.mem_range.mpr (winIdx_lt h3 h4)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  push_cast
  have hlogT : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
  have hfib : ∀ k ∈ Finset.range n,
      (∑ u ∈ S with winIdx 0 u = k, (mult u : ℝ)) ≤ C * Real.log (T + 2) := by
    intro k hk
    have hkT : (k : ℝ) < T := by
      have := Finset.mem_range.mp hk
      rw [hn, sub_zero] at this
      exact (Nat.lt_ceil).mp this
    have hsub : (↑(S.filter (fun u => winIdx 0 u = k)) : Set ℂ) ⊆ zeroSet k (k + 1) := by
      intro u hu
      rw [Finset.coe_filter] at hu
      obtain ⟨hu, hk'⟩ := hu
      obtain ⟨h0, h1, h2, h3, _⟩ := hS hu
      obtain ⟨s1, s2⟩ := winIdx_spec h3
      rw [hk', zero_add] at s1 s2
      exact ⟨h0, h1, h2, s1, s2⟩
    have := hC k _ hsub
    push_cast at this
    rw [abs_of_nonneg (Nat.cast_nonneg k)] at this
    refine this.trans ?_
    gcongr
  refine (Finset.sum_le_sum hfib).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hn1 : (n : ℝ) ≤ T + 1 := by
    rw [hn, sub_zero]; exact (Nat.ceil_lt_add_one hT).le
  have : 0 ≤ C * Real.log (T + 2) := mul_nonneg hC0 hlogT
  nlinarith

/-- **`N(T) ≪ T log T`** (with multiplicity): `N(T) ≤ C (T+1) log(T+2)` for all `T ≥ 0`. -/
theorem zeroCount_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
    (zeroCount T : ℝ) ≤ C * (T + 1) * Real.log (T + 2) := by
  obtain ⟨C, hC0, hC⟩ := sum_mult_le
  exact ⟨C, hC0, fun T hT => hC T hT _ (by intro u hu; exact (Set.Finite.mem_toFinset _).mp hu)⟩

/-- The same in the form `N(T) ≤ C T log T` for `T ≥ 2`. -/
theorem zeroCount_le_T_log_T : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T →
    (zeroCount T : ℝ) ≤ C * T * Real.log T := by
  obtain ⟨C, hC0, hC⟩ := zeroCount_le
  refine ⟨3 * C, by positivity, fun T hT => (hC T (by linarith)).trans ?_⟩
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have h2 : Real.log (T + 2) ≤ 2 * Real.log T := by
    rw [← Real.log_rpow (by linarith)]
    apply Real.log_le_log (by linarith)
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    push_cast
    nlinarith
  have h3 : T + 1 ≤ 3 / 2 * T := by linarith
  have hl2 : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
  calc C * (T + 1) * Real.log (T + 2) ≤ C * (3 / 2 * T) * (2 * Real.log T) := by gcongr
    _ = 3 * C * T * Real.log T := by ring

/-- Zeros on the critical line are counted by `N(T)`: `#{t ∈ S} ≤ N(T)` for every finite set `S`
of ordinates `0 < t ≤ T` of zeros `L(Δ, 6+it) = 0`. -/
lemma critical_card_le_zeroCount {T : ℝ} (S : Finset ℝ)
    (hS : ∀ t ∈ S, 0 < t ∧ t ≤ T ∧ tauL (6 + t * I) = 0) : S.card ≤ zeroCount T := by
  classical
  set f : ℝ → ℂ := fun t => 6 + t * I
  have hinj : Set.InjOn f S := by
    intro x _ y _ h
    have := congrArg Complex.im h
    simpa [f] using this
  have hsub : S.image f ⊆ (zeroSet_finite 0 T).toFinset := by
    intro u hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨h0, h1, h2⟩ := hS t ht
    rw [Set.Finite.mem_toFinset]
    refine ⟨h2, ?_, ?_, ?_, ?_⟩ <;> simp [f] <;> norm_num <;> linarith
  calc S.card = (S.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ ∑ u ∈ S.image f, mult u := card_le_sum_mult _ fun u hu => by
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
        exact (hS t ht).2.2
    _ ≤ ∑ u ∈ (zeroSet_finite 0 T).toFinset, mult u := Finset.sum_le_sum_of_subset hsub
    _ = zeroCount T := rfl

/-- **Two-sided count** `T ≪ N(T) ≪ T log T`.  The lower bound counts only zeros on the critical
line (Hafner, `HardyCountHafner.tauL_critical_zeros_linear`). -/
theorem zeroCount_two_sided : ∃ c C T₀ : ℝ, 0 < c ∧ 0 ≤ C ∧ 2 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
    c * T ≤ zeroCount T ∧ (zeroCount T : ℝ) ≤ C * T * Real.log T := by
  obtain ⟨c, T₁, hc, hlow⟩ := HardyCountHafner.tauL_critical_zeros_linear
  obtain ⟨C, hC0, hup⟩ := zeroCount_le_T_log_T
  refine ⟨c, C, max T₁ 2, hc, hC0, le_max_right _ _, fun T hT => ⟨?_, hup T ?_⟩⟩
  · obtain ⟨S, hS, hcard⟩ := hlow T (le_trans (le_max_left _ _) hT)
    exact hcard.trans (by exact_mod_cast critical_card_le_zeroCount S hS)
  · exact le_trans (le_max_right _ _) hT

end RamanujanTau.ZeroCount
