import RamanujanTau.BLBound.Modules

/-!
# Lower bounds for Boylan–Webb's threshold

`b_ℓ(m) ≤ 2m - 1` is `bEll_le`. This file gives a criterion for equality.

* `not_mem_bSet`: if `L(2k+1) ∉ Λ^odd(2k+3, m)`, then `X : Λ^odd(2k+1, m) → Λ^odd(2k+3, m)`
  is not a bijection.
* `bEll_eq_of_not_mem`: if this holds for every `k ≤ m - 2`, then `b_ℓ(m) = 2m - 1`.
* `not_mem_of_errors`: an `ℓ`-adic criterion. Suppose `L(2n+3) - κ L(2n+1) = ℓ^(n+1) G_n`, and a
  linear functional `obs` sees `L(2n+1)` and `U G_n`, but not `U L(2n+1)`, modulo `ℓ`. Then
  `L(2k+1) ∉ Λ^odd(2k+3, m)` whenever `k + 2 ≤ m`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanTau.BLBound
open PowerSeries AtkinOBrienFinal BoylanWebb AtkinOBrien

noncomputable section

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

lemma Xm_mapsTo (m k : ℕ) :
    Set.MapsTo (Xm ℓ m) (Lam ℓ m (2 * k + 1)) (Lam ℓ m (2 * (k + 1) + 1)) := by
  intro x hx
  rw [SetLike.mem_coe, ← Xm_map]
  exact Submodule.mem_map_of_mem hx

lemma Lam_anti (m k : ℕ) : Lam ℓ m (2 * (k + 1) + 1) ≤ Lam ℓ m (2 * k + 1) := by
  apply Submodule.span_mono
  rintro _ ⟨i, hi, rfl⟩
  exact ⟨i, by omega, rfl⟩

lemma Xm_iterate_mapsTo (m k j : ℕ) :
    Set.MapsTo (Xm ℓ m)^[j] (Lam ℓ m (2 * k + 1)) (Lam ℓ m (2 * (k + j) + 1)) := by
  induction j with
  | zero => exact fun x hx => hx
  | succ j ih =>
    intro x hx
    rw [Function.iterate_succ_apply', show k + (j + 1) = (k + j) + 1 by ring]
    exact Xm_mapsTo m (k + j) (ih hx)

/-- If `L(2k+1)` is missing from `Λ^odd(2k+3, m)`, then `2k+1` is not in the stable range. -/
theorem not_mem_bSet (h13 : 13 ≤ ℓ) (m : ℕ) (hm : 1 ≤ m) (k : ℕ)
    (h : redm ℓ m (L ℓ (2 * k + 1)) ∉ Lam ℓ m (2 * (k + 1) + 1)) :
    2 * k + 1 ∉ bSet ℓ m := by
  rintro ⟨-, hmaps, hinj, -⟩
  rw [show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by ring] at hmaps
  set s : Set (PowerSeries (Rm ℓ m)) := ↑(Lam ℓ m (2 * k + 1))
  set t : Set (PowerSeries (Rm ℓ m)) := ↑(Lam ℓ m (2 * (k + 1) + 1))
  have hts : t ⊆ s := Lam_anti m k
  have hself : Set.MapsTo (Xm ℓ m) s s := fun x hx => hts (hmaps hx)
  -- `s` is finite: a high iterate of `X` embeds it in the stable module.
  obtain ⟨-, hfinS⟩ := chain_structure h13 m hm (k + m) (by omega)
  have hfinHigh : (Lam ℓ m (2 * (k + m) + 1) : Set (PowerSeries (Rm ℓ m))).Finite := by
    haveI := hfinS
    exact Set.toFinite _
  have hs : s.Finite :=
    Set.Finite.of_finite_image
      (hfinHigh.subset (Set.image_subset_iff.mpr (Xm_iterate_mapsTo m k m)))
      (hinj.iterate hself m)
  have hL : redm ℓ m (L ℓ (2 * k + 1)) ∈ s := Submodule.subset_span ⟨k, le_rfl, rfl⟩
  have hss : t ⊂ s := Set.ssubset_iff_subset_ne.mpr ⟨hts, fun he => h (show _ ∈ t from he ▸ hL)⟩
  have hlt := Set.ncard_lt_ncard hss hs
  have hle := Set.ncard_le_ncard_of_injOn _ hmaps hinj (hs.subset hts)
  omega

/-- **Equality criterion for `b_ℓ(m)`.** -/
theorem bEll_eq_of_not_mem (h13 : 13 ≤ ℓ) (m : ℕ) (hm : 1 ≤ m)
    (h : ∀ k, k + 2 ≤ m → redm ℓ m (L ℓ (2 * k + 1)) ∉ Lam ℓ m (2 * (k + 1) + 1)) :
    bEll ℓ m = 2 * m - 1 := by
  apply le_antisymm (bEll_le h13 m hm)
  have hne : (bSet ℓ m).Nonempty := ⟨_, mem_bSet h13 m hm (m - 1) (by omega)⟩
  obtain ⟨⟨k, hk⟩, hmem⟩ := Nat.sInf_mem hne
  by_contra hlt
  have hlt' : sInf (bSet ℓ m) < 2 * m - 1 := by
    unfold bEll at hlt
    omega
  apply not_mem_bSet h13 m hm k (h k (by omega))
  rw [← hk]
  exact Nat.sInf_mem hne

/-! ### An `ℓ`-adic criterion -/

/-- Lift a series modulo `ℓ^m` coefficientwise. -/
def liftPS (m : ℕ) (V : PowerSeries (Rm ℓ m)) : PS ℓ :=
  PowerSeries.mk fun n => (((coeff n V).val : ℕ) : ℤ_[ℓ])

lemma map_liftPS (m : ℕ) (V : PowerSeries (Rm ℓ m)) :
    PowerSeries.map (PadicInt.toZModPow (p := ℓ) m) (liftPS m V) = V := by
  ext n
  rw [coeff_map, liftPS, coeff_mk, map_natCast, ZMod.natCast_zmod_val]

/-- A series vanishing modulo `ℓ^m` is divisible by `ℓ^m`. -/
lemma Dvd_of_map_eq_zero (m : ℕ) {F : PS ℓ}
    (h : PowerSeries.map (PadicInt.toZModPow (p := ℓ) m) F = 0) :
    Dvd (ℓ : ℤ_[ℓ]) m F := by
  have hc : ∀ n, ∃ d : ℤ_[ℓ], coeff n F = (ℓ : ℤ_[ℓ]) ^ m * d := by
    intro n
    have hn : coeff n F ∈ RingHom.ker (PadicInt.toZModPow (p := ℓ) m) := by
      rw [RingHom.mem_ker, ← coeff_map, h, map_zero]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at hn
    obtain ⟨d, hd⟩ := hn
    exact ⟨d, by rw [← hd, mul_comm]⟩
  choose d hd using hc
  refine ⟨PowerSeries.mk d, ?_⟩
  ext n
  rw [coeff_smul, coeff_mk, hd, smul_eq_mul]

lemma map_smul_PS (m : ℕ) (c : ℤ_[ℓ]) (F : PS ℓ) :
    PowerSeries.map (PadicInt.toZModPow (p := ℓ) m) (c • F) =
      PadicInt.toZModPow m c • PowerSeries.map (PadicInt.toZModPow (p := ℓ) m) F := by
  rw [PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C]

lemma unit_of_toZMod_ne_zero {x : ℤ_[ℓ]} (hx : PadicInt.toZMod x ≠ 0) : IsUnit x := by
  by_contra hn
  apply hx
  have hz : x ∈ IsLocalRing.maximalIdeal ℤ_[ℓ] := (IsLocalRing.mem_maximalIdeal _).mpr hn
  rwa [← PadicInt.ker_toZMod, RingHom.mem_ker] at hz

lemma toZMod_prime : PadicInt.toZMod (ℓ : ℤ_[ℓ]) = 0 := by
  rw [map_natCast, ZMod.natCast_self]

/-- **`ℓ`-adic criterion for `L(2k+1) ∉ Λ^odd(2k+3, m)`.** -/
theorem not_mem_of_errors (κ : ℤ_[ℓ]) (G : ℕ → PS ℓ) (obs : PS ℓ →ₗ[ℤ_[ℓ]] ℤ_[ℓ])
    (hrec : ∀ n, Ll ℓ (2 * n + 3) - κ • Ll ℓ (2 * n + 1) = (ℓ : ℤ_[ℓ]) ^ (n + 1) • G n)
    (hodd : ∀ n, PadicInt.toZMod (obs (Ll ℓ (2 * n + 1))) ≠ 0)
    (heven : ∀ n, PadicInt.toZMod (obs (Ulin ℓ (Ll ℓ (2 * n + 1)))) = 0)
    (herr : ∀ n, PadicInt.toZMod (obs (Ulin ℓ (G n))) ≠ 0)
    (m k : ℕ) (hk : k + 2 ≤ m) :
    redm ℓ m (L ℓ (2 * k + 1)) ∉ Lam ℓ m (2 * (k + 1) + 1) := by
  intro hmem
  set π := PadicInt.toZModPow (p := ℓ) m
  have hred : ∀ b, redm ℓ m (L ℓ b) = PowerSeries.map π (Ll ℓ b) := fun b =>
    (toZModPow_Ll m b).symm
  set A := Ll ℓ (2 * (k + 1) + 1)
  -- Step 1: every later odd iterate is a multiple of `A` modulo `ℓ^(k+2)`.
  have hstep : ∀ j, Dvd (ℓ : ℤ_[ℓ]) (k + 2) (Ll ℓ (2 * (k + 1 + j) + 1) - κ ^ j • A) := by
    intro j
    induction j with
    | zero => exact ⟨0, by simp [A]⟩
    | succ j ih =>
      have hr := hrec (k + 1 + j)
      have he : Ll ℓ (2 * (k + 1 + (j + 1)) + 1) - κ ^ (j + 1) • A =
          κ • (Ll ℓ (2 * (k + 1 + j) + 1) - κ ^ j • A) +
            (ℓ : ℤ_[ℓ]) ^ (k + 1 + j + 1) • G (k + 1 + j) := by
        rw [← hr, show 2 * (k + 1 + (j + 1)) + 1 = 2 * (k + 1 + j) + 3 by ring, smul_sub,
          pow_succ', mul_smul]
        abel
      rw [he]
      exact Dvd_add (Dvd_smul _ ih) (Dvd_mono (by omega) ⟨G (k + 1 + j), rfl⟩)
  -- Step 2: the same modulo `ℓ^m`, for every element of the module.
  set ϖ : Rm ℓ m := (ℓ : Rm ℓ m) ^ (k + 2)
  have hP : ∀ y ∈ Lam ℓ m (2 * (k + 1) + 1),
      ∃ a : Rm ℓ m, ∃ V : PowerSeries (Rm ℓ m), y = a • PowerSeries.map π A + ϖ • V := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      obtain ⟨W, hW⟩ := hstep (i - (k + 1))
      rw [show k + 1 + (i - (k + 1)) = i by omega] at hW
      refine ⟨π κ ^ (i - (k + 1)), PowerSeries.map π W, ?_⟩
      have hm := congrArg (PowerSeries.map π) hW
      rw [map_sub, map_smul_PS, map_smul_PS, map_pow, map_pow, map_natCast] at hm
      rw [hred, ← sub_eq_iff_eq_add', hm]
    | zero => exact ⟨0, 0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, V, rfl⟩ := hx
      obtain ⟨b, W, rfl⟩ := hy
      exact ⟨a + b, V + W, by rw [add_smul, smul_add]; abel⟩
    | smul c x _ hx =>
      obtain ⟨a, V, rfl⟩ := hx
      exact ⟨c * a, c • V, by rw [smul_add, mul_smul, smul_comm c ϖ]⟩
  obtain ⟨a, V, hV⟩ := hP _ hmem
  -- Step 3: lift to `ℤ_ℓ`.
  set ã : ℤ_[ℓ] := ((a.val : ℕ) : ℤ_[ℓ])
  have hã : π ã = a := by rw [map_natCast, ZMod.natCast_zmod_val]
  have hD : Dvd (ℓ : ℤ_[ℓ]) (k + 2)
      (Ll ℓ (2 * k + 1) - ã • A) := by
    have h0 : PowerSeries.map π
        (Ll ℓ (2 * k + 1) - ã • A - (ℓ : ℤ_[ℓ]) ^ (k + 2) • liftPS m V) = 0 := by
      rw [map_sub, map_sub, map_smul_PS, map_smul_PS, map_liftPS, hã, map_pow, map_natCast,
        ← hred, hV]
      abel
    obtain ⟨E, hE⟩ := Dvd_of_map_eq_zero m h0
    refine ⟨(ℓ : ℤ_[ℓ]) ^ (m - (k + 2)) • E + liftPS m V, ?_⟩
    rw [smul_add, ← mul_smul, ← pow_add, show k + 2 + (m - (k + 2)) = m by omega, ← hE]
    abel
  -- Step 4: two scalar observations.
  have hobs : ∀ f : PS ℓ →ₗ[ℤ_[ℓ]] ℤ_[ℓ], ∃ w : ℤ_[ℓ],
      (1 - ã * κ) * f (Ll ℓ (2 * k + 1)) - ã * (ℓ : ℤ_[ℓ]) ^ (k + 1) * f (G k) =
        (ℓ : ℤ_[ℓ]) ^ (k + 2) * w := by
    intro f
    obtain ⟨E, hE⟩ := hD
    refine ⟨f E, ?_⟩
    have hA : A = κ • Ll ℓ (2 * k + 1) + (ℓ : ℤ_[ℓ]) ^ (k + 1) • G k := by
      show Ll ℓ (2 * (k + 1) + 1) = _
      rw [← hrec k, show 2 * (k + 1) + 1 = 2 * k + 3 by ring]
      abel
    have h1 := congrArg f hE
    rw [hA, map_sub, map_smul, map_add, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, smul_eq_mul] at h1
    rw [← h1]
    ring
  obtain ⟨w1, hw1⟩ := hobs obs
  obtain ⟨w2, hw2⟩ := hobs (obs ∘ₗ Ulin ℓ)
  simp only [LinearMap.comp_apply] at hw2
  obtain ⟨u, hu⟩ := unit_of_toZMod_ne_zero (hodd k)
  set t : ℤ_[ℓ] := (ã * obs (G k) + (ℓ : ℤ_[ℓ]) * w1) * ↑u⁻¹
  have ht : 1 - ã * κ = (ℓ : ℤ_[ℓ]) ^ (k + 1) * t := by
    have hx : obs (Ll ℓ (2 * k + 1)) * ↑u⁻¹ = 1 := by rw [← hu, Units.mul_inv]
    calc 1 - ã * κ = ((1 - ã * κ) * obs (Ll ℓ (2 * k + 1))) * ↑u⁻¹ := by
          rw [mul_assoc, hx, mul_one]
      _ = _ := by
        rw [show (1 - ã * κ) * obs (Ll ℓ (2 * k + 1)) = (ℓ : ℤ_[ℓ]) ^ (k + 1) * (ã * obs (G k) + ℓ * w1) by
          rw [pow_succ] at hw1; linear_combination hw1]
        simp only [t]
        ring
  have hcancel : t * obs (Ulin ℓ (Ll ℓ (2 * k + 1))) - ã * obs (Ulin ℓ (G k)) =
      (ℓ : ℤ_[ℓ]) * w2 := by
    apply mul_left_cancel₀ (pow_ne_zero (k + 1) (by exact_mod_cast hℓ.out.ne_zero :
      (ℓ : ℤ_[ℓ]) ≠ 0))
    rw [ht] at hw2
    rw [pow_succ] at hw2
    linear_combination hw2
  have hz := congrArg PadicInt.toZMod hcancel
  simp only [map_sub, map_mul] at hz
  rw [heven k, toZMod_prime, mul_zero, zero_mul, zero_sub, neg_eq_zero] at hz
  have ha0 : PadicInt.toZMod ã = 0 := (mul_eq_zero.mp hz).resolve_right (herr k)
  have h1 := congrArg PadicInt.toZMod ht
  simp only [map_sub, map_one, map_mul, map_pow] at h1
  rw [ha0, zero_mul, sub_zero, toZMod_prime, zero_pow (Nat.succ_ne_zero k), zero_mul] at h1
  exact one_ne_zero h1

/-! ### Scalar recurrences -/

/-- A stable step of the chain with finite modules lies in `bSet`. -/
theorem mem_bSet_of_eq (m k₀ : ℕ)
    (heq : Lam ℓ m (2 * k₀ + 1) = Lam ℓ m (2 * (k₀ + 1) + 1))
    (hfin : Finite (Lam ℓ m (2 * k₀ + 1))) : 2 * k₀ + 1 ∈ bSet ℓ m := by
  refine ⟨⟨k₀, rfl⟩, ?_⟩
  rw [show 2 * k₀ + 1 + 2 = 2 * (k₀ + 1) + 1 by ring]
  have hmap := Xm_map (ℓ := ℓ) m k₀
  have hmaps := Xm_mapsTo (ℓ := ℓ) m k₀
  have hsurj : Set.SurjOn (Xm ℓ m) (Lam ℓ m (2 * k₀ + 1)) (Lam ℓ m (2 * (k₀ + 1) + 1)) := by
    intro y hy
    rw [SetLike.mem_coe, ← hmap] at hy
    obtain ⟨x, hx, he⟩ := hy
    exact ⟨x, hx, he⟩
  refine ⟨hmaps, ?_, hsurj⟩
  let T : Lam ℓ m (2 * k₀ + 1) → Lam ℓ m (2 * k₀ + 1) :=
    fun x => ⟨Xm ℓ m x, by
      have h := hmaps x.2
      rw [SetLike.mem_coe, ← heq] at h
      exact h⟩
  have hTs : Function.Surjective T := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, he⟩ := hsurj (show y ∈ (Lam ℓ m (2 * (k₀ + 1) + 1) : Set _) from heq ▸ hy)
    exact ⟨⟨x, hx⟩, Subtype.ext he⟩
  have hTi := Finite.injective_iff_surjective.mpr hTs
  intro x hx y hy hxy
  exact congrArg Subtype.val (@hTi ⟨x, hx⟩ ⟨y, hy⟩ (Subtype.ext hxy))

/-- **Upper bound from a scalar recurrence.** If `ℓ^m ∣ L(2j+3) - κ L(2j+1)` for every
`j ≥ k₀`, with `κ` a unit, then `2k₀+1` is in the stable range. -/
theorem mem_bSet_of_scalar (m k₀ : ℕ) (κ : ℤ_[ℓ]) (hκ : PadicInt.toZMod κ ≠ 0)
    (h : ∀ j, k₀ ≤ j → Dvd (ℓ : ℤ_[ℓ]) m (Ll ℓ (2 * j + 3) - κ • Ll ℓ (2 * j + 1))) :
    2 * k₀ + 1 ∈ bSet ℓ m := by
  set π := PadicInt.toZModPow (p := ℓ) m
  have hz : (π (ℓ : ℤ_[ℓ])) ^ m = 0 := by
    rw [map_natCast, ← Nat.cast_pow, ZMod.natCast_self]
  have hstep : ∀ j, k₀ ≤ j → gm ℓ m (j + 1) = π κ • gm ℓ m j := by
    intro j hj
    obtain ⟨V, hV⟩ := h j hj
    have hm := congrArg (PowerSeries.map π) hV
    rw [map_sub, map_smul_PS, map_smul_PS, map_pow, hz, zero_smul, sub_eq_zero] at hm
    simp only [gm, ← toZModPow_Ll]
    rw [show 2 * (j + 1) + 1 = 2 * j + 3 by ring]
    exact hm
  have hpow : ∀ i, gm ℓ m (k₀ + i) = π κ ^ i • gm ℓ m k₀ := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [← add_assoc, hstep _ (by omega), ih, smul_smul, pow_succ, mul_comm]
  -- `π κ` is a unit.
  obtain ⟨u, hu⟩ := unit_of_toZMod_ne_zero hκ
  have hunit : IsUnit (π κ) := by rw [← hu]; exact u.isUnit.map π
  have hspan : ∀ k, k₀ ≤ k → Lam ℓ m (2 * k + 1) = Submodule.span (Rm ℓ m) {gm ℓ m k₀} := by
    intro k hk
    apply le_antisymm
    · rw [Lam_eq]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      rw [show k + j = k₀ + (k - k₀ + j) by omega, hpow]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      obtain ⟨v, hv⟩ := hunit.pow (k - k₀)
      have hg : gm ℓ m k₀ = (↑v⁻¹ : Rm ℓ m) • gm ℓ m k := by
        rw [show k = k₀ + (k - k₀) by omega, hpow, smul_smul, ← hv, Units.inv_mul, one_smul]
      rw [SetLike.mem_coe, hg]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, le_rfl, rfl⟩)
  haveI : NeZero (ℓ ^ m) := ⟨pow_ne_zero m hℓ.out.ne_zero⟩
  apply mem_bSet_of_eq m k₀ (by rw [hspan k₀ le_rfl, hspan (k₀ + 1) (by omega)])
  rw [hspan k₀ le_rfl]
  haveI : Module.Finite (Rm ℓ m) (Submodule.span (Rm ℓ m) {gm ℓ m k₀}) :=
    Module.Finite.span_singleton _ _
  exact Module.finite_of_finite (Rm ℓ m)

/-- **Lower bound from failure of a scalar recurrence.** Suppose that, modulo `ℓ^e`,
every later odd iterate is `κ^j L(2k+3)`; that `L(2k+3) ≡ κ L(2k+1)` modulo `ℓ`; that
`L(2k+1)` has a unit coefficient; and that no scalar `c` gives `L(2k+3) ≡ c L(2k+1)`
modulo `ℓ^e`. Then `L(2k+1) ∉ Λ^odd(2k+3, m)` for every `m ≥ e`. -/
theorem not_mem_of_scalar (κ : ℤ_[ℓ]) (k e m : ℕ) (hem : e ≤ m)
    (hlater : ∀ j, Dvd (ℓ : ℤ_[ℓ]) e
      (Ll ℓ (2 * (k + 1 + j) + 1) - κ ^ j • Ll ℓ (2 * (k + 1) + 1)))
    (hone : Dvd (ℓ : ℤ_[ℓ]) 1 (Ll ℓ (2 * (k + 1) + 1) - κ • Ll ℓ (2 * k + 1)))
    (n : ℕ) (hn : PadicInt.toZMod (coeff n (Ll ℓ (2 * k + 1))) ≠ 0)
    (hfail : ∀ c : ℤ_[ℓ], ¬ Dvd (ℓ : ℤ_[ℓ]) e
      (Ll ℓ (2 * (k + 1) + 1) - c • Ll ℓ (2 * k + 1))) :
    redm ℓ m (L ℓ (2 * k + 1)) ∉ Lam ℓ m (2 * (k + 1) + 1) := by
  intro hmem
  set π := PadicInt.toZModPow (p := ℓ) m
  have hred : ∀ b, redm ℓ m (L ℓ b) = PowerSeries.map π (Ll ℓ b) := fun b =>
    (toZModPow_Ll m b).symm
  set A := Ll ℓ (2 * (k + 1) + 1)
  set ϖ : Rm ℓ m := (ℓ : Rm ℓ m) ^ e
  have hP : ∀ y ∈ Lam ℓ m (2 * (k + 1) + 1),
      ∃ a : Rm ℓ m, ∃ V : PowerSeries (Rm ℓ m), y = a • PowerSeries.map π A + ϖ • V := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      obtain ⟨W, hW⟩ := hlater (i - (k + 1))
      rw [show k + 1 + (i - (k + 1)) = i by omega] at hW
      refine ⟨π κ ^ (i - (k + 1)), PowerSeries.map π W, ?_⟩
      have hm := congrArg (PowerSeries.map π) hW
      rw [map_sub, map_smul_PS, map_smul_PS, map_pow, map_pow, map_natCast] at hm
      rw [hred, ← sub_eq_iff_eq_add', hm]
    | zero => exact ⟨0, 0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, V, rfl⟩ := hx
      obtain ⟨b, W, rfl⟩ := hy
      exact ⟨a + b, V + W, by rw [add_smul, smul_add]; abel⟩
    | smul c x _ hx =>
      obtain ⟨a, V, rfl⟩ := hx
      exact ⟨c * a, c • V, by rw [smul_add, mul_smul, smul_comm c ϖ]⟩
  obtain ⟨a, V, hV⟩ := hP _ hmem
  set ã : ℤ_[ℓ] := ((a.val : ℕ) : ℤ_[ℓ])
  have hã : π ã = a := by rw [map_natCast, ZMod.natCast_zmod_val]
  have hD : Dvd (ℓ : ℤ_[ℓ]) e (Ll ℓ (2 * k + 1) - ã • A) := by
    have h0 : PowerSeries.map π
        (Ll ℓ (2 * k + 1) - ã • A - (ℓ : ℤ_[ℓ]) ^ e • liftPS m V) = 0 := by
      rw [map_sub, map_sub, map_smul_PS, map_smul_PS, map_liftPS, hã, map_pow, map_natCast,
        ← hred, hV]
      abel
    obtain ⟨E, hE⟩ := Dvd_of_map_eq_zero m h0
    refine ⟨(ℓ : ℤ_[ℓ]) ^ (m - e) • E + liftPS m V, ?_⟩
    rw [smul_add, ← mul_smul, ← pow_add, show e + (m - e) = m by omega, ← hE]
    abel
  -- `ã κ ≡ 1` modulo `ℓ`, so `ã` is a unit.
  have he1 : 1 ≤ e := by
    by_contra h0
    exact hfail 0 ⟨_, by rw [show e = 0 by omega, pow_zero, one_smul]⟩
  have hmod : Dvd (ℓ : ℤ_[ℓ]) 1 ((1 - ã * κ) • Ll ℓ (2 * k + 1)) := by
    have := Dvd_add (Dvd_mono he1 hD) (Dvd_smul ã hone)
    convert this using 1
    rw [sub_smul, one_smul, mul_smul, smul_sub]
    abel
  obtain ⟨W, hW⟩ := hmod
  have hc := congrArg (fun F => PadicInt.toZMod (coeff n F)) hW
  simp only [coeff_smul, smul_eq_mul, map_mul, pow_one, toZMod_prime, zero_mul] at hc
  have h1 : PadicInt.toZMod (1 - ã * κ) = 0 := (mul_eq_zero.mp hc).resolve_right hn
  have hãu : PadicInt.toZMod ã ≠ 0 := by
    intro h0
    rw [map_sub, map_one, map_mul, h0, zero_mul, sub_zero] at h1
    exact one_ne_zero h1
  obtain ⟨w, hw⟩ := unit_of_toZMod_ne_zero hãu
  apply hfail (↑w⁻¹)
  obtain ⟨E, hE⟩ := hD
  refine ⟨-(↑w⁻¹ : ℤ_[ℓ]) • E, ?_⟩
  have : A - (↑w⁻¹ : ℤ_[ℓ]) • Ll ℓ (2 * k + 1) =
      -(↑w⁻¹ : ℤ_[ℓ]) • (Ll ℓ (2 * k + 1) - ã • A) := by
    rw [smul_sub, smul_smul, ← hw, neg_mul, Units.inv_mul]
    simp only [neg_smul, one_smul]
    abel
  rw [this, hE, smul_comm]

end

end RamanujanTau.BLBound
