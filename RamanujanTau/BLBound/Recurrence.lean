import RamanujanTau.BLBound.Rank

/-!
# Partition congruences with `R` terms

With `R = ⌊(ℓ+12)/24⌋`, the module `Λ^odd(2m-1,m)` is spanned by the `R` consecutive terms `L(2k+1), …, L(2k+2R-1)`
for every `k ≥ m-1`. Hence each term of the partition chain is, modulo `ℓ^m`, a fixed integer combination of the
`R` terms before it, and of the `R` terms after it, from index `2m-1` on. This is the shape of the theorem of
Folsom–Kent–Ono, with the threshold of Boylan–Webb.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanTau.BLBound
open PowerSeries AtkinOBrien AtkinOBrienFinal BoylanWebb

noncomputable section

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-! ### Cyclic modules -/

/-- An orbit spanning a finite-dimensional space is spanned by its first `dim` terms. -/
lemma krylov_vec {F Q : Type*} [Field F] [AddCommGroup Q] [Module F Q] [Module.Finite F Q]
    (T : Q →ₗ[F] Q) (e : ℕ → Q) (he : ∀ n, T (e n) = e (n + 1))
    (hspan : Submodule.span F (Set.range e) = ⊤) {R : ℕ} (hR : Module.finrank F Q ≤ R) :
    Submodule.span F (e '' Set.Iio R) = ⊤ := by
  let W : ℕ → Submodule F Q := fun j => Submodule.span F (e '' Set.Iio j)
  have hmono : ∀ {i j : ℕ}, i ≤ j → W i ≤ W j := by
    intro i j hij
    exact Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio hij))
  have hmem : ∀ {i j : ℕ}, i < j → e i ∈ W j := by
    intro i j hij
    exact Submodule.subset_span ⟨i, hij, rfl⟩
  have hstep : ∀ j, e j ∈ W j → W j = ⊤ := by
    intro j hj
    have hT : ∀ v ∈ W j, T v ∈ W j := by
      intro v hv
      have hle : W j ≤ (W j).comap T := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨i, hi, rfl⟩
        change T (e i) ∈ W j
        rw [he]
        rcases Nat.lt_or_ge (i + 1) j with h | h
        · exact hmem h
        · have : i + 1 = j := by
            have : i < j := hi
            omega
          rw [this]
          exact hj
      exact hle hv
    have hall : ∀ n, e n ∈ W j := by
      intro n
      induction n with
      | zero =>
        rcases Nat.eq_zero_or_pos j with h | h
        · rw [← h]
          exact hj
        · exact hmem h
      | succ n ih =>
        rw [← he]
        exact hT _ ih
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    exact hall n
  have hclaim : ∀ j, W j = ⊤ ∨ j ≤ Module.finrank F (W j) := by
    intro j
    induction j with
    | zero => exact Or.inr (Nat.zero_le _)
    | succ j ih =>
      rcases ih with h | h
      · exact Or.inl (top_le_iff.mp (h ▸ hmono (Nat.le_succ j)))
      · by_cases hj : e j ∈ W j
        · exact Or.inl (top_le_iff.mp (hstep j hj ▸ hmono (Nat.le_succ j)))
        · refine Or.inr ?_
          have hlt : W j < W (j + 1) :=
            lt_of_le_of_ne (hmono (Nat.le_succ j)) fun he' => hj (he' ▸ hmem (Nat.lt_succ_self j))
          have := Submodule.finrank_lt_finrank_of_lt hlt
          omega
  have hd : W (Module.finrank F Q) = ⊤ := by
    rcases hclaim (Module.finrank F Q) with h | h
    · exact h
    · exact Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) h)
  exact top_le_iff.mp (hd ▸ hmono hR)

/-- An additive subgroup containing a set contains its span over `ℤ/p`. -/
lemma mem_of_span_set {Q : Type*} [AddCommGroup Q] {p : ℕ} [hp : Fact p.Prime] [Module (ZMod p) Q]
    (H : AddSubgroup Q) (S : Set Q) (hS : ∀ v ∈ S, v ∈ H) {x : Q}
    (hx : x ∈ Submodule.span (ZMod p) S) : x ∈ H := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact hS y hy
  | zero => exact H.zero_mem
  | add y z _ _ hy hz => exact H.add_mem hy hz
  | smul c y _ hy =>
    rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
    exact H.nsmul_mem hy _

/-- The quotient step of `krylov_of_socle`. -/
lemma krylov_quot {A Q : Type*} [AddCommGroup A] [AddCommGroup Q] {p R : ℕ} [hp : Fact p.Prime]
    [Module (ZMod p) Q] [Finite Q] (hc : Nat.card Q ≤ p ^ R) (π : A →+ Q) (hπ : Function.Surjective π)
    (Tb : Q →+ Q) (x : ℕ → A) (hTb : ∀ n, Tb (π (x n)) = π (x (n + 1)))
    (hgen : AddSubgroup.closure (Set.range x) = ⊤) (a : A) :
    π a ∈ (AddSubgroup.closure (x '' Set.Iio R)).map π := by
  haveI : Module.Finite (ZMod p) Q := Module.Finite.of_finite
  have hrk : Module.finrank (ZMod p) Q ≤ R := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod] at hc
    exact (Nat.pow_le_pow_iff_right hp.out.one_lt).mp hc
  have hspan : Submodule.span (ZMod p) (Set.range fun n => π (x n)) = ⊤ := by
    rw [eq_top_iff]
    rintro q -
    obtain ⟨a, rfl⟩ := hπ q
    have ha : a ∈ AddSubgroup.closure (Set.range x) := by
      rw [hgen]
      trivial
    induction ha using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨n, rfl⟩ := hy
      exact Submodule.subset_span ⟨n, rfl⟩
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add y z _ _ hy hz =>
      rw [map_add]
      exact Submodule.add_mem _ hy hz
    | neg y _ hy =>
      rw [map_neg]
      exact Submodule.neg_mem _ hy
  have hk := krylov_vec (Tb.toZModLinearMap p) (fun n => π (x n)) hTb hspan hrk
  refine mem_of_span_set (p := p) _ ((fun n => π (x n)) '' Set.Iio R) ?_ ?_
  · rintro _ ⟨i, hi, rfl⟩
    exact ⟨x i, AddSubgroup.subset_closure ⟨i, hi, rfl⟩, rfl⟩
  · rw [hk]
    exact Submodule.mem_top

/-- An orbit generating a finite abelian group, killed by `p^m` and with at most `p^R` elements of order dividing
`p`, is generated by its first `R` terms. -/
lemma krylov_of_socle {A : Type*} [AddCommGroup A] [Finite A] {p m R : ℕ} [hp : Fact p.Prime]
    (hm : ∀ x : A, (p ^ m) • x = 0) (hc : Nat.card {x : A // p • x = 0} ≤ p ^ R)
    (T : A →+ A) (x : ℕ → A) (hx : ∀ n, T (x n) = x (n + 1))
    (hgen : AddSubgroup.closure (Set.range x) = ⊤) :
    AddSubgroup.closure (x '' Set.Iio R) = ⊤ := by
  let f : A →+ A := nsmulAddMonoidHom p
  have hQ : ∀ q : A ⧸ f.range, p • q = 0 := by
    intro q
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact ⟨a, rfl⟩
  letI : Module (ZMod p) (A ⧸ f.range) := AddCommGroup.zmodModule hQ
  have hT : f.range ≤ f.range.comap T := by
    rintro _ ⟨y, rfl⟩
    exact ⟨T y, by simp [f]⟩
  let Tb : (A ⧸ f.range) →+ (A ⧸ f.range) := QuotientAddGroup.map _ _ T hT
  have hcq : Nat.card (A ⧸ f.range) ≤ p ^ R := by
    rw [card_quot_eq p]
    exact hc
  refine top_of_gen hm _ fun a => ?_
  obtain ⟨h, hh, he⟩ := krylov_quot (A := A) (Q := A ⧸ f.range) hcq (QuotientAddGroup.mk' f.range)
    (QuotientAddGroup.mk_surjective) Tb x (fun n => by
      change QuotientAddGroup.mk (T (x n)) = _
      rw [hx]
      rfl) hgen a
  obtain ⟨y, hy⟩ := QuotientAddGroup.eq.mp he
  refine ⟨h, hh, y, ?_⟩
  have hy' : p • y = -h + a := hy
  rw [hy']
  abel

/-! ### The module -/

lemma Xm_gm (m k : ℕ) : Xm ℓ m (gm ℓ m k) = gm ℓ m (k + 1) := Xm_L m k

/-- **`R` consecutive terms span `Λ^odd`.** -/
theorem krylov_Lam (h13 : 13 ≤ ℓ) (m : ℕ) (hm : 1 ≤ m) (k₀ : ℕ) (hk : m ≤ k₀ + 1) :
    Lam ℓ m (2 * k₀ + 1) ≤ Submodule.span (Rm ℓ m)
      (Set.range fun i : Fin ((ℓ + 12) / 24) => gm ℓ m (k₀ + i)) := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  haveI : NeZero (ℓ ^ (n + 1)) := ⟨pow_ne_zero _ hℓ.out.ne_zero⟩
  obtain ⟨heq, hfin⟩ := chain_structure (ℓ := ℓ) h13 (n + 1) hm k₀ hk
  haveI : Finite (Lam ℓ (n + 1) (2 * k₀ + 1)) := hfin
  have hkill : ∀ x : Lam ℓ (n + 1) (2 * k₀ + 1), (ℓ ^ (n + 1)) • x = 0 := by
    intro x
    have hz : ((ℓ ^ (n + 1) : ℕ) : Rm ℓ (n + 1)) = 0 := ZMod.natCast_self _
    apply Subtype.ext
    ext i
    change PowerSeries.coeff i ((ℓ ^ (n + 1)) • (x : PowerSeries (Rm ℓ (n + 1)))) = PowerSeries.coeff i 0
    rw [map_nsmul, nsmul_eq_mul, hz, zero_mul, map_zero]
  have hmemg : ∀ j, gm ℓ (n + 1) (k₀ + j) ∈ Lam ℓ (n + 1) (2 * k₀ + 1) := by
    intro j
    rw [Lam_eq]
    exact Submodule.subset_span ⟨j, rfl⟩
  have hXmem : ∀ v, v ∈ Lam ℓ (n + 1) (2 * k₀ + 1) → Xm ℓ (n + 1) v ∈ Lam ℓ (n + 1) (2 * k₀ + 1) := by
    intro v hv
    rw [heq, ← Xm_map]
    exact Submodule.mem_map_of_mem hv
  let T : Lam ℓ (n + 1) (2 * k₀ + 1) →+ Lam ℓ (n + 1) (2 * k₀ + 1) :=
    { toFun := fun v => ⟨Xm ℓ (n + 1) v, hXmem v v.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ _ _) }
  let x : ℕ → Lam ℓ (n + 1) (2 * k₀ + 1) := fun j => ⟨gm ℓ (n + 1) (k₀ + j), hmemg j⟩
  have hx : ∀ j, T (x j) = x (j + 1) := fun j => Subtype.ext (Xm_gm _ _)
  have hgen : AddSubgroup.closure (Set.range x) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨v, hv⟩ -
    have key : ∀ w (hw : w ∈ Lam ℓ (n + 1) (2 * k₀ + 1)),
        (⟨w, hw⟩ : Lam ℓ (n + 1) (2 * k₀ + 1)) ∈ AddSubgroup.closure (Set.range x) := by
      intro w hw
      have hw' := hw
      rw [Lam_eq] at hw'
      induction hw' using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        exact AddSubgroup.subset_closure ⟨j, rfl⟩
      | zero => exact AddSubgroup.zero_mem _
      | add y z hy hz ihy ihz =>
        have hy' : y ∈ Lam ℓ (n + 1) (2 * k₀ + 1) := by rw [Lam_eq]; exact hy
        have hz' : z ∈ Lam ℓ (n + 1) (2 * k₀ + 1) := by rw [Lam_eq]; exact hz
        exact AddSubgroup.add_mem _ (ihy hy') (ihz hz')
      | smul c y hy ihy =>
        have hy' : y ∈ Lam ℓ (n + 1) (2 * k₀ + 1) := by rw [Lam_eq]; exact hy
        have e : (⟨c • y, hw⟩ : Lam ℓ (n + 1) (2 * k₀ + 1)) = c.val • (⟨y, hy'⟩ : Lam ℓ (n + 1) (2 * k₀ + 1)) := by
          apply Subtype.ext
          change c • y = c.val • y
          conv_lhs => rw [← ZMod.natCast_zmod_val c]
          rw [Nat.cast_smul_eq_nsmul]
        rw [e]
        exact AddSubgroup.nsmul_mem _ (ihy hy') _
    exact key v hv
  have hk' := krylov_of_socle hkill (card_socle_le h13 n k₀ hk) T x hx hgen
  have key : ∀ y : Lam ℓ (n + 1) (2 * k₀ + 1), y ∈ AddSubgroup.closure (x '' Set.Iio ((ℓ + 12) / 24)) →
      (y : PowerSeries (Rm ℓ (n + 1))) ∈ Submodule.span (Rm ℓ (n + 1))
        (Set.range fun i : Fin ((ℓ + 12) / 24) => gm ℓ (n + 1) (k₀ + i)) := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | neg y _ hy => exact Submodule.neg_mem _ hy
  intro v hv
  exact key ⟨v, hv⟩ (by rw [hk']; trivial)

/-- A linear relation among the `gm` persists along the chain. -/
lemma relation_shift {ι : Type*} [Fintype ι] {m k₀ s₀ : ℕ} {c : ι → Rm ℓ m} {s : ι → ℕ}
    (h : gm ℓ m (k₀ + s₀) = ∑ i, c i • gm ℓ m (k₀ + s i)) (j : ℕ) :
    gm ℓ m (k₀ + j + s₀) = ∑ i, c i • gm ℓ m (k₀ + j + s i) := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    have := congrArg (Xm ℓ m) ih
    rw [map_sum] at this
    simp only [map_smul, Xm_gm] at this
    rw [show k₀ + (j + 1) + s₀ = k₀ + j + s₀ + 1 by ring, this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show k₀ + (j + 1) + s i = k₀ + j + s i + 1 by ring]

/-- The relations, as series over `ℤ_ℓ`, for every index from `2m-1` on. -/
lemma series_of_relation {ι : Type*} [Fintype ι] (h5 : 5 ≤ ℓ) {m k₀ s₀ : ℕ} {c : ι → Rm ℓ m} {s : ι → ℕ}
    (h : gm ℓ m (k₀ + s₀) = ∑ i, c i • gm ℓ m (k₀ + s i)) (hne : NeZero (ℓ ^ m)) (b : ℕ) (hb : 2 * k₀ + 1 ≤ b) :
    ∃ y : PS ℓ, Ll ℓ (b + 2 * s₀) - ∑ i, (((c i).val : ℕ) : ℤ_[ℓ]) • Ll ℓ (b + 2 * s i) = ((ℓ : ℤ_[ℓ]) ^ m) • y := by
  have hodd : ∀ j, ∃ y : PS ℓ, Ll ℓ (2 * (k₀ + j) + 1 + 2 * s₀) -
      ∑ i, (((c i).val : ℕ) : ℤ_[ℓ]) • Ll ℓ (2 * (k₀ + j) + 1 + 2 * s i) = ((ℓ : ℤ_[ℓ]) ^ m) • y := by
    intro j
    have hr := relation_shift h j
    refine redP_eq_zero m ?_
    rw [map_sub, map_sum, sub_eq_zero]
    have hL : ∀ t, redP ℓ m (Ll ℓ (2 * (k₀ + j) + 1 + 2 * t)) = gm ℓ m (k₀ + j + t) := by
      intro t
      rw [toZModPow_Ll, gm]
      congr 2
      ring
    rw [hL, hr]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [redP_smul, map_natCast, ZMod.natCast_zmod_val, hL]
  obtain ⟨d, hd⟩ : ∃ d, b = 2 * (k₀ + d) + 1 ∨ b = 2 * (k₀ + d) + 2 :=
    ⟨(b - (2 * k₀ + 1)) / 2, by omega⟩
  rcases hd with rfl | rfl
  · exact hodd d
  · obtain ⟨y, hy⟩ := hodd d
    refine ⟨Ulin ℓ y, ?_⟩
    have hU : ∀ t, Ll ℓ (2 * (k₀ + d) + 2 + 2 * t) = Ulin ℓ (Ll ℓ (2 * (k₀ + d) + 1 + 2 * t)) := by
      intro t
      rw [show 2 * (k₀ + d) + 2 + 2 * t = 2 * (k₀ + d + t) + 2 by ring, even_U]
      congr 2
      ring
    have := congrArg (Ulin ℓ) hy
    rw [map_sub, map_sum, map_smul] at this
    simp only [map_smul] at this
    rw [← this, hU]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [hU]

/-- A relation among the series `Ll` gives a congruence among partition numbers. -/
lemma partition_of_series {ι : Type*} [Fintype ι] (h13 : 13 ≤ ℓ) {m b n s₀ : ℕ} {c : ι → ℕ} {s : ι → ℕ}
    (hn : 24 ∣ ℓ ^ b * n + 1) {y : PS ℓ}
    (hy : Ll ℓ (b + 2 * s₀) - ∑ i, ((c i : ℕ) : ℤ_[ℓ]) • Ll ℓ (b + 2 * s i) = ((ℓ : ℤ_[ℓ]) ^ m) • y) :
    (ℓ : ℤ) ^ m ∣ (Fintype.card (Nat.Partition ((ℓ ^ (b + 2 * s₀) * n + 1) / 24)) : ℤ) -
      ∑ i, (c i : ℤ) * (Fintype.card (Nat.Partition ((ℓ ^ (b + 2 * s i) * n + 1) / 24)) : ℤ) := by
  have h24' := RamanujanTau.TheoremA.HalfIntegral.h24 (ℓ := ℓ) h13
  obtain ⟨Q, hQ, hQe⟩ := L_factor_all (ℓ := ℓ) h24' b
  set φ := PowerSeries.map (Int.castRingHom ℤ_[ℓ]) with hφ
  obtain ⟨u, hu⟩ := hQ.map φ
  have hL : ∀ i, Ll ℓ (b + 2 * i) = (u : PS ℓ) * φ (Pser ℓ (b + 2 * i)) := by
    intro i
    change φ (L ℓ (b + 2 * i)) = _
    rw [hQe, map_mul, hu]
  have hsum : (u : PS ℓ) * (φ (Pser ℓ (b + 2 * s₀)) -
      ∑ i, ((c i : ℕ) : ℤ_[ℓ]) • φ (Pser ℓ (b + 2 * s i))) = ((ℓ : ℤ_[ℓ]) ^ m) • y := by
    rw [← hy, mul_sub, Finset.mul_sum, hL]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hL, mul_smul_comm]
  have hd : φ (Pser ℓ (b + 2 * s₀)) - ∑ i, ((c i : ℕ) : ℤ_[ℓ]) • φ (Pser ℓ (b + 2 * s i)) =
      ((ℓ : ℤ_[ℓ]) ^ m) • (↑u⁻¹ * y) := by
    rw [← mul_smul_comm, ← hsum, ← mul_assoc, Units.inv_mul, one_mul]
  obtain ⟨t, ht⟩ := index_shift_all (ℓ := ℓ) h24' b n (by exact_mod_cast hn)
  have hc2 := congrArg (coeff t) hd
  rw [map_sub, map_sum, coeff_smul, smul_eq_mul] at hc2
  have hval : ∀ j, coeff t (φ (Pser ℓ (b + 2 * j))) =
      (((Fintype.card (Nat.Partition ((ℓ ^ (b + 2 * j) * n + 1) / 24)) : ℤ) : ℤ) : ℤ_[ℓ]) := by
    intro j
    have e1 : ((ℓ : ℤ) ^ (b + 2 * j) * n + 1) / 24 = (((ℓ ^ (b + 2 * j) * n + 1) / 24 : ℕ) : ℤ) := by
      push_cast
      rfl
    rw [hφ, coeff_map, Pser, coeff_mk, ← ht j, e1, pZ_natCast, eq_intCast]
  simp only [coeff_smul, smul_eq_mul, hval] at hc2
  have hdvd : (ℓ : ℤ_[ℓ]) ^ m ∣ (((Fintype.card (Nat.Partition ((ℓ ^ (b + 2 * s₀) * n + 1) / 24)) : ℤ) -
      ∑ i, (c i : ℤ) * (Fintype.card (Nat.Partition ((ℓ ^ (b + 2 * s i) * n + 1) / 24)) : ℤ) : ℤ) : ℤ_[ℓ]) := by
    push_cast at hc2 ⊢
    exact ⟨_, hc2⟩
  exact (PadicInt.pow_p_dvd_int_iff _ _).mp hdvd

/-- **Each term is a combination of the `R` terms before it.** With `R = ⌊(ℓ+12)/24⌋`, there are integers
`a₀, …, a_{R-1}` depending only on `ℓ` and `m` with
`p((ℓ^{b+2R} n + 1)/24) ≡ ∑ aᵢ p((ℓ^{b+2i} n + 1)/24) (mod ℓ^m)` for all `b ≥ 2m-1` and all `n` with
`24 ∣ ℓ^b n + 1`. -/
theorem partition_recurrence (h13 : 13 ≤ ℓ) (m : ℕ) (hm : 1 ≤ m) :
    ∃ a : Fin ((ℓ + 12) / 24) → ℕ, ∀ b, 2 * m - 1 ≤ b → ∀ n : ℕ, 24 ∣ ℓ ^ b * n + 1 →
      (ℓ : ℤ) ^ m ∣ (Fintype.card (Nat.Partition ((ℓ ^ (b + 2 * ((ℓ + 12) / 24)) * n + 1) / 24)) : ℤ) -
        ∑ i, (a i : ℤ) * (Fintype.card (Nat.Partition ((ℓ ^ (b + 2 * (i : ℕ)) * n + 1) / 24)) : ℤ) := by
  have h5 : 5 ≤ ℓ := by omega
  haveI hne : NeZero (ℓ ^ m) := ⟨pow_ne_zero _ hℓ.out.ne_zero⟩
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, m = k₀ + 1 := ⟨m - 1, by omega⟩
  have hmem : gm ℓ m (k₀ + (ℓ + 12) / 24) ∈ Lam ℓ m (2 * k₀ + 1) := by
    rw [Lam_eq]
    exact Submodule.subset_span ⟨_, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (Rm ℓ m)).mp
    (krylov_Lam h13 m hm k₀ hk₀.le hmem)
  refine ⟨fun i => (c i).val, fun b hb n hn => ?_⟩
  obtain ⟨y, hy⟩ := series_of_relation (s := fun i : Fin ((ℓ + 12) / 24) => (i : ℕ)) h5 hc.symm hne b (by omega)
  exact partition_of_series h13 hn hy

/-- **Each term is a combination of the `R` terms after it.** -/
theorem partition_recurrence_back (h13 : 13 ≤ ℓ) (m : ℕ) (hm : 1 ≤ m) :
    ∃ d : Fin ((ℓ + 12) / 24) → ℕ, ∀ b, 2 * m - 1 ≤ b → ∀ n : ℕ, 24 ∣ ℓ ^ b * n + 1 →
      (ℓ : ℤ) ^ m ∣ (Fintype.card (Nat.Partition ((ℓ ^ b * n + 1) / 24)) : ℤ) -
        ∑ i, (d i : ℤ) * (Fintype.card (Nat.Partition ((ℓ ^ (b + 2 * ((i : ℕ) + 1)) * n + 1) / 24)) : ℤ) := by
  have h5 : 5 ≤ ℓ := by omega
  haveI hne : NeZero (ℓ ^ m) := ⟨pow_ne_zero _ hℓ.out.ne_zero⟩
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, m = k₀ + 1 := ⟨m - 1, by omega⟩
  obtain ⟨heq, -⟩ := chain_structure (ℓ := ℓ) h13 m hm k₀ hk₀.le
  have hmem : gm ℓ m k₀ ∈ Lam ℓ m (2 * (k₀ + 1) + 1) := by
    rw [← heq, Lam_eq]
    exact Submodule.subset_span ⟨0, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (Rm ℓ m)).mp
    (krylov_Lam h13 m hm (k₀ + 1) (by omega) hmem)
  have hc' : gm ℓ m (k₀ + 0) = ∑ i, c i • gm ℓ m (k₀ + ((i : ℕ) + 1)) := by
    rw [add_zero, ← hc]
    exact Finset.sum_congr rfl fun i _ => by rw [show k₀ + ((i : ℕ) + 1) = k₀ + 1 + (i : ℕ) by ring]
  refine ⟨fun i => (c i).val, fun b hb n hn => ?_⟩
  obtain ⟨y, hy⟩ := series_of_relation h5 hc' hne b (by omega)
  simpa using partition_of_series (s₀ := 0) h13 hn hy

end

end RamanujanTau.BLBound
