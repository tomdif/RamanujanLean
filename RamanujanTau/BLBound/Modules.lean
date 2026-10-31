import RamanujanTau.BLBound.Main

/-!
# Boylan–Webb's modules and invariants

This file defines the modules `Λ^odd(b,m)`, the threshold `b_ℓ(m)` and the invariant `d_ℓ` as in Boylan–Webb
(Trans. AMS 365, 2013, Theorem 1.4, Remark 1 and (5.1)), and proves `b_ℓ(m) ≤ 2m-1` and `d_ℓ = 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanTau.BLBound
open PowerSeries AtkinOBrienFinal BoylanWebb

noncomputable section

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

/-- Coefficients modulo `ℓ^m`. -/
abbrev Rm (m : ℕ) : Type := ZMod (ℓ ^ m)

/-- Reduction modulo `ℓ^m`. -/
abbrev redm (m : ℕ) : PowerSeries ℤ →+* PowerSeries (Rm ℓ m) :=
  PowerSeries.map (Int.castRingHom (Rm ℓ m))

/-- `X = D ∘ U`, modulo `ℓ^m`. -/
def Xm (m : ℕ) : Module.End (Rm ℓ m) (PowerSeries (Rm ℓ m)) where
  toFun f := U ℓ (redm ℓ m (Φ ℓ) * U ℓ f)
  map_add' f g := by rw [U_add, mul_add, U_add]
  map_smul' c f := by
    simp only [RingHom.id_apply, PowerSeries.smul_eq_C_mul]
    rw [U_C_mul, mul_left_comm, U_C_mul]

/-- `Λ^odd(b,m)`: the span modulo `ℓ^m` of `L(β)` for odd `β ≥ b`. -/
def Lam (m b : ℕ) : Submodule (Rm ℓ m) (PowerSeries (Rm ℓ m)) :=
  Submodule.span (Rm ℓ m) {g | ∃ k : ℕ, b ≤ 2 * k + 1 ∧ g = redm ℓ m (L ℓ (2 * k + 1))}

/-- The set of odd `b` for which `X : Λ^odd(b,m) → Λ^odd(b+2,m)` is an isomorphism. -/
def bSet (m : ℕ) : Set ℕ := {b | Odd b ∧ Set.BijOn (Xm ℓ m) (Lam ℓ m b) (Lam ℓ m (b + 2))}

/-- **Boylan–Webb's `b_ℓ(m)`.** -/
def bEll (m : ℕ) : ℕ := sInf (bSet ℓ m)

variable {ℓ}

lemma Xm_L (m k : ℕ) : Xm ℓ m (redm ℓ m (L ℓ (2 * k + 1))) = redm ℓ m (L ℓ (2 * (k + 1) + 1)) := by
  have e2 : L ℓ (2 * k + 2) = U ℓ (L ℓ (2 * k + 1)) := by
    rw [show 2 * k + 2 = (2 * k + 1) + 1 by ring, L_succ, T, if_neg (not_even_2b1 k)]
  have e3 : L ℓ (2 * (k + 1) + 1) = U ℓ (Φ ℓ * L ℓ (2 * k + 2)) := by
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, L_succ, T, if_pos ⟨k + 1, by ring⟩]
  change U ℓ (redm ℓ m (Φ ℓ) * U ℓ (redm ℓ m (L ℓ (2 * k + 1)))) = _
  rw [e3, e2, map_U, map_mul, map_U]

/-- `Ll` reduces to `L` modulo `ℓ^m`. -/
lemma toZModPow_Ll (m b : ℕ) :
    PowerSeries.map (PadicInt.toZModPow (p := ℓ) m) (Ll ℓ b) = redm ℓ m (L ℓ b) := by
  ext n
  simp [Ll, PowerSeries.coeff_map]

/-- The relation modulo `ℓ^m`. -/
theorem relation_m (h13 : 13 ≤ ℓ) {χ : Polynomial ℤ}
    (hχ : ∀ v ∈ Vbar ℓ, Polynomial.aeval (Xbar ℓ) (χ.map (Int.castRingHom (ZMod ℓ))) v = 0)
    (m : ℕ) (hm : 1 ≤ m) (b : ℕ) (hb : 2 * m - 1 ≤ b) :
    ∑ i ∈ Finset.range ((χ ^ m).natDegree + 1),
      ((χ ^ m).coeff i : Rm ℓ m) • redm ℓ m (L ℓ (b + 2 * i)) = 0 := by
  have h5 : 5 ≤ ℓ := by omega
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨y, hy⟩ := chi_series h13 h5 hχ m' b (by omega)
  have h := congrArg (PowerSeries.map (PadicInt.toZModPow (p := ℓ) (m' + 1))) hy
  rw [map_sum, PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, map_pow, map_natCast] at h
  have hz : ((ℓ : ℕ) : ZMod (ℓ ^ (m' + 1))) ^ (m' + 1) = 0 := by
    rw [← Nat.cast_pow]
    exact ZMod.natCast_self _
  rw [hz, map_zero, zero_mul] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, toZModPow_Ll, Int.cast_smul_eq_zsmul]

/-- The generators of `Λ^odd`. -/
def gm (ℓ : ℕ) [Fact ℓ.Prime] (m k : ℕ) : PowerSeries (Rm ℓ m) := redm ℓ m (L ℓ (2 * k + 1))

lemma Lam_eq (m k : ℕ) :
    Lam ℓ m (2 * k + 1) = Submodule.span (Rm ℓ m) {g | ∃ j : ℕ, g = gm ℓ m (k + j)} := by
  unfold Lam
  congr 1
  ext g
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i - k, by rw [gm, show k + (i - k) = i by omega]⟩
  · rintro ⟨j, rfl⟩
    exact ⟨k + j, by omega, rfl⟩

/-- **The structure of the chain.** The two ends of the relation give the three facts about `Λ^odd`. -/
theorem chain_structure (h13 : 13 ≤ ℓ) (m : ℕ) (hm : 1 ≤ m) (k₀ : ℕ) (hk : m ≤ k₀ + 1) :
    Lam ℓ m (2 * k₀ + 1) = Lam ℓ m (2 * (k₀ + 1) + 1) ∧ Finite (Lam ℓ m (2 * k₀ + 1)) := by
  classical
  have h5 : 5 ≤ ℓ := by omega
  obtain ⟨χ, hmon, hc, hχ⟩ := exists_chi (ℓ := ℓ) h13
  set p := χ ^ m with hp
  have hpm : p.Monic := hmon.pow m
  set N := p.natDegree with hN
  have hrel : ∀ k, k₀ ≤ k → ∑ i ∈ Finset.range (N + 1), (p.coeff i : Rm ℓ m) • gm ℓ m (k + i) = 0 := by
    intro k hk'
    have := relation_m h13 hχ m hm (2 * k + 1) (by omega)
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) this
    rw [gm, show 2 * (k + i) + 1 = 2 * k + 1 + 2 * i by ring]
  have hc0 : p.coeff 0 = χ.coeff 0 ^ m := by
    rw [hp, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow, ← Polynomial.coeff_zero_eq_eval_zero]
  have hprime : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ.out
  have hcop : IsCoprime (χ.coeff 0) (ℓ : ℤ) := ((Prime.coprime_iff_not_dvd hprime).mpr hc).symm
  obtain ⟨u, v, huv⟩ : IsCoprime (p.coeff 0) ((ℓ : ℤ) ^ m) := by
    rw [hc0]
    exact hcop.pow
  have hunit : ((u : Rm ℓ m)) * (p.coeff 0 : Rm ℓ m) = 1 := by
    have h1 := congrArg (Int.cast : ℤ → Rm ℓ m) huv
    have hz : (((ℓ : ℤ) ^ m : ℤ) : Rm ℓ m) = 0 := by
      have := ZMod.natCast_self (ℓ ^ m)
      push_cast at this ⊢
      exact this
    push_cast at h1 hz
    rw [hz, mul_zero, add_zero] at h1
    exact h1
  have hfront : ∀ k, k₀ ≤ k → gm ℓ m k ∈ Lam ℓ m (2 * (k + 1) + 1) := by
    intro k hk'
    have hr := hrel k hk'
    rw [Finset.sum_range_succ', add_zero] at hr
    have hmem : ∑ i ∈ Finset.range N, (p.coeff (i + 1) : Rm ℓ m) • gm ℓ m (k + (i + 1)) ∈
        Lam ℓ m (2 * (k + 1) + 1) := by
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
      rw [Lam_eq]
      exact Submodule.subset_span ⟨i, by rw [gm, gm]; congr 3; ring⟩
    have heq : gm ℓ m k = -(u : Rm ℓ m) • ∑ i ∈ Finset.range N, (p.coeff (i + 1) : Rm ℓ m) • gm ℓ m (k + (i + 1)) := by
      have e : (p.coeff 0 : Rm ℓ m) • gm ℓ m k =
          -∑ i ∈ Finset.range N, (p.coeff (i + 1) : Rm ℓ m) • gm ℓ m (k + (i + 1)) :=
        eq_neg_of_add_eq_zero_right hr
      calc gm ℓ m k = ((u : Rm ℓ m) * (p.coeff 0 : Rm ℓ m)) • gm ℓ m k := by rw [hunit, one_smul]
        _ = _ := by rw [mul_smul, e, smul_neg, neg_smul]
    rw [heq]
    exact Submodule.smul_mem _ _ hmem
  have hback : ∀ n : ℕ, gm ℓ m (k₀ + n) ∈ Submodule.span (Rm ℓ m)
      ((fun i => gm ℓ m (k₀ + i)) '' (Finset.range N : Set ℕ)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      by_cases hn : n < N
      · exact Submodule.subset_span ⟨n, by simpa using hn, rfl⟩
      · have hk' : k₀ ≤ k₀ + (n - N) := by omega
        have hr := hrel _ hk'
        rw [Finset.sum_range_succ] at hr
        have hNc : (p.coeff N : Rm ℓ m) = 1 := by
          have : p.coeff N = 1 := hpm.coeff_natDegree
          rw [this]
          simp
        rw [hNc, one_smul, show k₀ + (n - N) + N = k₀ + n by omega] at hr
        rw [eq_neg_of_add_eq_zero_right hr]
        refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_)
        have hi' : i < N := Finset.mem_range.mp hi
        have := ih (n - N + i) (by omega)
        rwa [show k₀ + (n - N + i) = k₀ + (n - N) + i by ring] at this
  refine ⟨?_, ?_⟩
  · apply le_antisymm
    · rw [Lam_eq m k₀]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · exact hfront k₀ le_rfl
      · rw [Lam_eq]
        exact Submodule.subset_span ⟨j - 1, by rw [gm, gm]; congr 3; omega⟩
    · rw [Lam_eq m (k₀ + 1), Lam_eq m k₀]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      exact Submodule.subset_span ⟨j + 1, by rw [gm, gm]; congr 3; omega⟩
  · haveI : NeZero (ℓ ^ m) := ⟨pow_ne_zero m hℓ.out.ne_zero⟩
    have hle : Lam ℓ m (2 * k₀ + 1) ≤ Submodule.span (Rm ℓ m)
        ((fun i => gm ℓ m (k₀ + i)) '' (Finset.range N : Set ℕ)) := by
      rw [Lam_eq]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      exact hback j
    have hfin : Set.Finite ((fun i => gm ℓ m (k₀ + i)) '' (Finset.range N : Set ℕ)) :=
      (Finset.finite_toSet _).image _
    haveI : Module.Finite (Rm ℓ m) (Submodule.span (Rm ℓ m)
        ((fun i => gm ℓ m (k₀ + i)) '' (Finset.range N : Set ℕ))) :=
      Module.Finite.span_of_finite _ hfin
    haveI : Finite (Submodule.span (Rm ℓ m)
        ((fun i => gm ℓ m (k₀ + i)) '' (Finset.range N : Set ℕ))) :=
      Module.finite_of_finite (Rm ℓ m)
    exact Finite.of_injective _ (Submodule.inclusion_injective hle)

/-- `X` maps the module at `k₀` onto the module at `k₀ + 1`. -/
lemma Xm_map (m k₀ : ℕ) :
    (Lam ℓ m (2 * k₀ + 1)).map (Xm ℓ m) = Lam ℓ m (2 * (k₀ + 1) + 1) := by
  rw [Lam_eq, Lam_eq, Submodule.map_span]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, by rw [gm, Xm_L, gm]; congr 3; omega⟩
  · rintro ⟨j, rfl⟩
    exact ⟨_, ⟨j, rfl⟩, by rw [gm, Xm_L, gm]; congr 3; omega⟩

/-- **Every odd `b ≥ 2m - 1` is in the stable range.** -/
theorem mem_bSet (h13 : 13 ≤ ℓ) (m : ℕ) (hm : 1 ≤ m) (k₀ : ℕ) (hk : m ≤ k₀ + 1) :
    2 * k₀ + 1 ∈ bSet ℓ m := by
  obtain ⟨heq, hfin⟩ := chain_structure h13 m hm k₀ hk
  refine ⟨⟨k₀, rfl⟩, ?_⟩
  rw [show 2 * k₀ + 1 + 2 = 2 * (k₀ + 1) + 1 by ring]
  have hmap := Xm_map (ℓ := ℓ) m k₀
  have hmaps : Set.MapsTo (Xm ℓ m) (Lam ℓ m (2 * k₀ + 1)) (Lam ℓ m (2 * (k₀ + 1) + 1)) := by
    intro x hx
    rw [← hmap]
    exact Submodule.mem_map_of_mem hx
  have hsurj : Set.SurjOn (Xm ℓ m) (Lam ℓ m (2 * k₀ + 1)) (Lam ℓ m (2 * (k₀ + 1) + 1)) := by
    intro y hy
    rw [← hmap] at hy
    obtain ⟨x, hx, he⟩ := hy
    exact ⟨x, hx, he⟩
  refine ⟨hmaps, ?_, hsurj⟩
  have hself : ∀ x, x ∈ Lam ℓ m (2 * k₀ + 1) → Xm ℓ m x ∈ Lam ℓ m (2 * k₀ + 1) := by
    intro x hx
    have := hmaps hx
    rwa [← heq] at this
  let T : Lam ℓ m (2 * k₀ + 1) → Lam ℓ m (2 * k₀ + 1) := fun x => ⟨Xm ℓ m x, hself x x.2⟩
  have hTs : Function.Surjective T := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, he⟩ := hsurj (show y ∈ (Lam ℓ m (2 * (k₀ + 1) + 1) : Set _) from heq ▸ hy)
    exact ⟨⟨x, hx⟩, Subtype.ext he⟩
  have hTi := Finite.injective_iff_surjective.mpr hTs
  intro x hx y hy hxy
  have := @hTi ⟨x, hx⟩ ⟨y, hy⟩ (Subtype.ext hxy)
  exact congrArg Subtype.val this

/-- **Boylan–Webb's threshold: `b_ℓ(m) ≤ 2m - 1` for every prime `ℓ ≥ 13`.** -/
theorem bEll_le (h13 : 13 ≤ ℓ) (m : ℕ) (hm : 1 ≤ m) : bEll ℓ m ≤ 2 * m - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have := mem_bSet h13 (k + 1) hm k le_rfl
  rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
  exact Nat.sInf_le this

/-! ### The invariant `d_ℓ` and the structure of `X̄` -/

/-- Reductions of weight `ℓ - 1` cusp forms. -/
def Sbar (ℓ : ℕ) [Fact ℓ.Prime] : Submodule (ZMod ℓ) (PowerSeries (ZMod ℓ)) where
  carrier := {v | FormBar ℓ (ℓ - 1) v ∧ PowerSeries.coeff 0 v = 0}
  zero_mem' := ⟨⟨0, MvPolynomial.isWeightedHomogeneous_zero _ _ _, map_zero _⟩, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨⟨P, hP, rfl⟩, h0⟩ ⟨⟨Q, hQ, rfl⟩, h1⟩
    exact ⟨⟨P + Q, hP.add hQ, map_add _ _ _⟩, by rw [map_add, h0, h1, add_zero]⟩
  smul_mem' := by
    rintro c _ ⟨⟨P, hP, rfl⟩, h0⟩
    refine ⟨⟨MvPolynomial.C c * P, hP.C_mul c, ?_⟩, ?_⟩
    · rw [map_mul, ModP.ev_C, PowerSeries.smul_eq_C_mul]
    · rw [map_smul, h0, smul_zero]

/-- The largest subspace of `S̄` on which `X̄` is bijective. -/
def Vinv (ℓ : ℕ) [Fact ℓ.Prime] : Submodule (ZMod ℓ) (PowerSeries (ZMod ℓ)) :=
  sSup {S | S ≤ Sbar ℓ ∧ Set.BijOn (Xbar ℓ) S S}

/-- **Boylan–Webb's `d_ℓ`** (5.1): the least `t` with `D̄ f · X̄^t ∈ V_inv` for all `f ∈ M_{ℓ-1}`. -/
def dEll (ℓ : ℕ) [Fact ℓ.Prime] : ℕ :=
  sInf {t | ∀ f, FormBar ℓ (ℓ - 1) f → (Xbar ℓ ^ t) (Dbar ℓ f) ∈ Vinv ℓ}

lemma Vbar_le_Sbar (h13 : 13 ≤ ℓ) : Vbar ℓ ≤ Sbar ℓ := by
  rintro _ ⟨a, ha, rfl⟩
  have h5 : 5 ≤ ℓ := by omega
  refine ⟨formBar_of_intForm ℓ h5 ℓ (ℓ - 1) (by omega) _ (intForm_V h13 ha), ?_⟩
  rw [PowerSeries.coeff_map, coeff_zero_V ha, map_zero]

/-- `Ū` preserves `S̄`. -/
lemma U_mem_formBar (h13 : 13 ≤ ℓ) {v : PowerSeries (ZMod ℓ)} (hv : v ∈ Sbar ℓ) :
    FormBar ℓ (ℓ - 1) (U ℓ v) := by
  have h5 : 5 ≤ ℓ := by omega
  have hp := hℓ.out
  obtain ⟨⟨P, hP, rfl⟩, h0⟩ := hv
  obtain ⟨c, hc, hcΨ⟩ := lift_iso ℓ _ P hP
  have hodd : ℓ % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h <;> omega
  set k := ℓ - 1 with hk
  have hn' : 4 * ModP.bexp0 k + 6 * ModP.bexp1 k = k := by
    unfold ModP.bexp0 ModP.bexp1
    omega
  set m := RamanujanTau.Mod691.p4 ^ ModP.bexp0 k * RamanujanTau.Mod691.p6 ^ ModP.bexp1 k with hm
  have hmF : IntForm (k : ℤ) m := (IntForm.mono _ _).cast (by rw [hn'])
  have hm0 : PowerSeries.constantCoeff m = 1 := by
    rw [hm, map_mul, map_pow, map_pow]
    have h4 : PowerSeries.constantCoeff RamanujanTau.Mod691.p4 = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, RamanujanTau.Mod691.coeff_p4]; simp
    have h6 : PowerSeries.constantCoeff RamanujanTau.Mod691.p6 = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, RamanujanTau.Mod691.coeff_p6]; simp
    rw [h4, h6, one_pow, one_pow, one_mul]
  have hc0 : (Int.castRingHom (ZMod ℓ)) (PowerSeries.coeff 0 c) = 0 := by
    have e : PowerSeries.coeff 0 (Ψ ℓ c) = 0 := by rw [hcΨ]; exact h0
    rwa [PowerSeries.coeff_map] at e
  set a := c - PowerSeries.C (PowerSeries.coeff 0 c) * m with ha
  have haF : IntForm (k : ℤ) a := hc.sub (hmF.C_mul _)
  have ha0 : PowerSeries.coeff 0 a = 0 := by
    rw [ha, map_sub, PowerSeries.coeff_zero_eq_constantCoeff_apply (PowerSeries.C _ * m), map_mul,
      PowerSeries.constantCoeff_C, hm0, mul_one, sub_self]
  have hΨa : Ψ ℓ a = ModP.ev (ZMod ℓ) P := by
    rw [ha, map_sub, map_mul, PowerSeries.map_C, hcΨ, hc0, map_zero, zero_mul, sub_zero]
  have hT := haF.hecke ℓ (ℓ - 2) (by
    rw [hk]
    push_cast [Nat.cast_sub (show 2 ≤ ℓ by omega), Nat.cast_sub (show 1 ≤ ℓ by omega)]
    ring) ha0
  have h := formBar_of_intForm ℓ h5 ℓ k (by omega) _ hT
  rwa [Ψ_hecke ℓ (ℓ - 2) (by omega), hΨa] at h

/-- `X̄` maps `S̄` into `V̄`. -/
theorem Xbar_range (h13 : 13 ≤ ℓ) {v : PowerSeries (ZMod ℓ)} (hv : v ∈ Sbar ℓ) : Xbar ℓ v ∈ Vbar ℓ := by
  obtain ⟨a, ha, he⟩ := D_image h13 (U_mem_formBar h13 hv)
  exact ⟨a, ha, he⟩

/-- **`V_inv = V̄`.** -/
theorem Vinv_eq (h13 : 13 ≤ ℓ) : Vinv ℓ = Vbar ℓ := by
  apply le_antisymm
  · refine sSup_le ?_
    rintro S ⟨hS, hb⟩ v hv
    obtain ⟨w, hw, rfl⟩ := hb.surjOn hv
    exact Xbar_range h13 (hS hw)
  · obtain ⟨S, -, hS⟩ := d_ell_zero (ℓ := ℓ) h13
    refine le_sSup ⟨Vbar_le_Sbar h13, ⟨fun v hv => Xbar_mem h13 hv, ?_, ?_⟩⟩
    · intro x hx y hy hxy
      exact sub_eq_zero.mp (Xbar_inj h13 (Submodule.sub_mem _ hx hy) (by rw [map_sub, hxy, sub_self]))
    · haveI := finite_Vbar (ℓ := ℓ) h13
      have hinj : Function.Injective (Tv (ℓ := ℓ) h13) := by
        rw [injective_iff_map_eq_zero]
        rintro ⟨v, hv⟩ h
        apply Subtype.ext
        exact Xbar_inj h13 hv (congrArg Subtype.val h)
      intro v hv
      obtain ⟨w, hw⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨v, hv⟩
      exact ⟨w, w.2, congrArg Subtype.val hw⟩

/-- **`d_ℓ = 0` for every prime `ℓ ≥ 13`**, the partition case of the Belmont–Lee–Musat–Trebat-Leder
conjecture. -/
theorem dEll_eq_zero (h13 : 13 ≤ ℓ) : dEll ℓ = 0 := by
  refine Nat.sInf_eq_zero.mpr (Or.inl ?_)
  intro f hf
  rw [pow_zero, Vinv_eq h13]
  obtain ⟨a, ha, he⟩ := D_image h13 hf
  exact ⟨a, ha, he⟩

/-- **`S̄ = V̄ ⊕ ker X̄`.** -/
theorem Sbar_decomp (h13 : 13 ≤ ℓ) {v : PowerSeries (ZMod ℓ)} (hv : v ∈ Sbar ℓ) :
    ∃ v' ∈ Vbar ℓ, Xbar ℓ (v - v') = 0 ∧ ∀ w ∈ Vbar ℓ, Xbar ℓ (v - w) = 0 → w = v' := by
  haveI := finite_Vbar (ℓ := ℓ) h13
  have hinj : Function.Injective (Tv (ℓ := ℓ) h13) := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨x, hx⟩ h
    apply Subtype.ext
    exact Xbar_inj h13 hx (congrArg Subtype.val h)
  obtain ⟨v', hv'⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨Xbar ℓ v, Xbar_range h13 hv⟩
  have hv2 : Xbar ℓ (v' : PowerSeries (ZMod ℓ)) = Xbar ℓ v := congrArg Subtype.val hv'
  refine ⟨v', v'.2, by rw [map_sub, hv2, sub_self], fun w hw hk => ?_⟩
  have hk2 : Xbar ℓ w = Xbar ℓ v := by
    rw [map_sub, sub_eq_zero] at hk
    exact hk.symm
  have h0 := Xbar_inj h13 (Submodule.sub_mem _ hw v'.2) (by rw [map_sub, hk2, hv2, sub_self])
  exact sub_eq_zero.mp h0

end

end RamanujanTau.BLBound
