import RamanujanTau.DBound.Decomp

/-!
# Approximate Katz series with valuation bounds: the ring structure

`Ap B f`: for every `N`, `f` is congruent mod `ℓ^N` to a finite Katz series `Σ a_i/E^i` with
`a_i ∈ B_i` and `ℓ^{B i} ∣ a_i`. (`Env c γ f` is `Ap (fun i => (max 0 (γ i − c)).toNat) f`.)

* `Ap_mul`: if `B₃ m ≤ B₁ k + B₂ l` whenever `m ≤ k + l`, then `Ap B₁ f → Ap B₂ g → Ap B₃ (f g)`.
  This is the statement "`B_E(r)` is a ring" (and `r^{-s}B_E(r) · r^{-t}B_E(r) ⊆ r^{-(s+t)}B_E(r)`),
  in coordinates; it rests on `decompN` (a product `b_k b_l / E^{k+l}` re-expands with indices `≤ k+l`).
* `Ap_add`, `Ap_smul`, `Ap_single`, `Ap_one`, `Ap_mono`, `Ap_of_isKatz`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace DBound
open MvPolynomial ModP AtkinOBrienFinal AtkinOBrien PowerSeries

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] (hℓ : 5 ≤ ℓ)

/-- `f ≡ Σ_{i<I} a_i/E^i (mod ℓ^N)` with `a_i ∈ B_i`, `ℓ^{B i} ∣ a_i`. -/
def KA (B : ℕ → ℕ) (N : ℕ) (f : PS ℓ) : Prop :=
  ∃ I, ∃ a : ℕ → Poly ℓ, (∀ i, a i ∈ Kpiece ℓ hℓ i) ∧ Approx ℓ hℓ N I a f ∧
    ∀ i, Dvd (ℓ : ℤ_[ℓ]) (B i) (a i)

/-- `f` has approximate Katz expansions with `v_i ≥ B i` to every precision. -/
def Ap (B : ℕ → ℕ) (f : PS ℓ) : Prop := ∀ N, KA hℓ B N f

lemma env_iff_Ap (c : ℤ) (γ : ℕ → ℤ) (f : PS ℓ) :
    Env ℓ hℓ c γ f ↔ Ap hℓ (fun i => (max 0 (γ i - c)).toNat) f := Iff.rfl

variable {hℓ}

/-- the Katz sum. -/
noncomputable abbrev ksum (I : ℕ) (a : ℕ → Poly ℓ) : PS ℓ :=
  ∑ i ∈ Finset.range I, ModP.ev ℤ_[ℓ] (a i) * Einv ℓ hℓ ^ i

lemma Dvd_mul_sub {N : ℕ} {f F g G : PS ℓ} (hf : Dvd (ℓ : ℤ_[ℓ]) N (f - F))
    (hg : Dvd (ℓ : ℤ_[ℓ]) N (g - G)) : Dvd (ℓ : ℤ_[ℓ]) N (f * g - F * G) := by
  obtain ⟨x, hx⟩ := hf; obtain ⟨y, hy⟩ := hg
  refine ⟨x * g + F * y, ?_⟩
  have : f * g - F * G = (f - F) * g + F * (g - G) := by ring
  rw [this, hx, hy, smul_add, smul_mul_assoc, mul_smul_comm]

lemma Dvd_sub_trans {N : ℕ} {f g h : PS ℓ} (h1 : Dvd (ℓ : ℤ_[ℓ]) N (f - g))
    (h2 : Dvd (ℓ : ℤ_[ℓ]) N (g - h)) : Dvd (ℓ : ℤ_[ℓ]) N (f - h) := by
  have := Dvd_add h1 h2
  rwa [sub_add_sub_cancel] at this

lemma Dvd_of_le {N M : ℕ} {M' : Type*} [AddCommGroup M'] [Module ℤ_[ℓ] M'] {x : M'} (h : N ≤ M)
    (hx : Dvd (ℓ : ℤ_[ℓ]) M x) : Dvd (ℓ : ℤ_[ℓ]) N x := Dvd_mono h hx

/-- **Product of two finite Katz series**, re-expanded mod `ℓ^N`. -/
theorem fin_mul (B₁ B₂ B₃ : ℕ → ℕ) (hB : ∀ k l m, m ≤ k + l → B₃ m ≤ B₁ k + B₂ l) (N I₁ I₂ : ℕ)
    (a b : ℕ → Poly ℓ) (ha : ∀ k, a k ∈ Kpiece ℓ hℓ k) (hb : ∀ l, b l ∈ Kpiece ℓ hℓ l)
    (hBa : ∀ k, Dvd (ℓ : ℤ_[ℓ]) (B₁ k) (a k)) (hBb : ∀ l, Dvd (ℓ : ℤ_[ℓ]) (B₂ l) (b l)) :
    ∃ c : ℕ → Poly ℓ, (∀ m, c m ∈ Kpiece ℓ hℓ m) ∧ (∀ m, Dvd (ℓ : ℤ_[ℓ]) (B₃ m) (c m)) ∧
      Dvd (ℓ : ℤ_[ℓ]) N (ksum (hℓ := hℓ) I₁ a * ksum (hℓ := hℓ) I₂ b - ksum (hℓ := hℓ) (I₁ + I₂) c) := by
  choose a' ha' using hBa
  choose b' hb' using hBb
  have ha'K : ∀ k, a' k ∈ Kpiece ℓ hℓ k := fun k =>
    Kpiece_of_smul hℓ (pow_ne_zero _ ell_ne_zero) (by rw [← ha' k]; exact ha k)
  have hb'K : ∀ l, b' l ∈ Kpiece ℓ hℓ l := fun l =>
    Kpiece_of_smul hℓ (pow_ne_zero _ ell_ne_zero) (by rw [← hb' l]; exact hb l)
  have hiso : ∀ k l, Iso (a' k * b' l) ((k + l) * (ℓ - 1)) := fun k l =>
    iso_of_eq ((iso_of_support hℓ ((mem_Kpiece hℓ).mp (ha'K k))).mul
      (iso_of_support hℓ ((mem_Kpiece hℓ).mp (hb'K l)))) (by rw [Nat.add_mul])
  choose cc hccK hcc0 hccD using fun k l => decompN hℓ N (k + l) (a' k * b' l) (hiso k l)
  set e : ℕ → ℕ → ℕ := fun k l => B₁ k + B₂ l with he
  refine ⟨fun m => ∑ k ∈ Finset.range I₁, ∑ l ∈ Finset.range I₂, (ℓ : ℤ_[ℓ]) ^ e k l • cc k l m,
    fun m => Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun l _ =>
      Submodule.smul_mem _ _ (hccK k l m), fun m => ?_, ?_⟩
  · refine Dvd.sum _ _ fun k _ => Dvd.sum _ _ fun l _ => ?_
    by_cases hm : m ≤ k + l
    · exact Dvd_mono (hB k l m hm) ⟨cc k l m, rfl⟩
    · rw [hcc0 k l m (by omega), smul_zero]; exact Dvd_zero _
  · -- the product, termwise
    have hprod : ksum (hℓ := hℓ) I₁ a * ksum (hℓ := hℓ) I₂ b =
        ∑ k ∈ Finset.range I₁, ∑ l ∈ Finset.range I₂, (ℓ : ℤ_[ℓ]) ^ e k l •
          (ModP.ev ℤ_[ℓ] (a' k * b' l) * Einv ℓ hℓ ^ (k + l)) := by
      rw [ksum, ksum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      rw [ha' k, hb' l, he]
      simp only [map_smul, map_mul]
      simp only [Algebra.smul_def, pow_add, map_pow, map_mul]
      ring
    have hsum : ksum (hℓ := hℓ) (I₁ + I₂)
        (fun m => ∑ k ∈ Finset.range I₁, ∑ l ∈ Finset.range I₂, (ℓ : ℤ_[ℓ]) ^ e k l • cc k l m) =
        ∑ k ∈ Finset.range I₁, ∑ l ∈ Finset.range I₂, (ℓ : ℤ_[ℓ]) ^ e k l •
          ∑ m ∈ Finset.range (k + l + 1), ModP.ev ℤ_[ℓ] (cc k l m) * Einv ℓ hℓ ^ m := by
      rw [ksum]
      simp only [map_sum, map_smul, Finset.sum_mul, smul_mul_assoc]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [Finset.smul_sum]
      symm
      refine Finset.sum_subset (Finset.range_subset_range.mpr (by
        have := Finset.mem_range.mp hk; have := Finset.mem_range.mp hl; omega)) fun m _ hm => ?_
      rw [hcc0 k l m (by rw [Finset.mem_range] at hm; omega), map_zero, zero_mul, smul_zero]
    rw [hprod, hsum, ← Finset.sum_sub_distrib]
    refine Dvd.sum _ _ fun k _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Dvd.sum _ _ fun l _ => ?_
    rw [← smul_sub]
    exact Dvd_smul _ (hccD k l)

/-- **`Ap` is multiplicative.** -/
theorem Ap_mul {B₁ B₂ B₃ : ℕ → ℕ} (hB : ∀ k l m, m ≤ k + l → B₃ m ≤ B₁ k + B₂ l) {f g : PS ℓ}
    (hf : Ap hℓ B₁ f) (hg : Ap hℓ B₂ g) : Ap hℓ B₃ (f * g) := by
  intro N
  obtain ⟨I₁, a, haK, haA, haB⟩ := hf N
  obtain ⟨I₂, b, hbK, hbA, hbB⟩ := hg N
  obtain ⟨c, hcK, hcB, hcD⟩ := fin_mul B₁ B₂ B₃ hB N I₁ I₂ a b haK hbK haB hbB
  exact ⟨I₁ + I₂, c, hcK, Dvd_sub_trans (Dvd_mul_sub haA hbA) hcD, hcB⟩

theorem Ap_add {B : ℕ → ℕ} {f g : PS ℓ} (hf : Ap hℓ B f) (hg : Ap hℓ B g) : Ap hℓ B (f + g) := by
  intro N
  obtain ⟨I₁, a, haK, ha, hab⟩ := hf N
  obtain ⟨I₂, b, hbK, hb, hbb⟩ := hg N
  exact ⟨max I₁ I₂, trunc I₁ a + trunc I₂ b, fun i => Submodule.add_mem _ (trunc_mem hℓ haK i)
    (trunc_mem hℓ hbK i), approx_add hℓ (approx_trunc hℓ ha (le_max_left _ _))
    (approx_trunc hℓ hb (le_max_right _ _)), fun i => Dvd_add (trunc_dvd i (hab i)) (trunc_dvd i (hbb i))⟩

theorem Ap_smul {B : ℕ → ℕ} (r : ℤ_[ℓ]) {f : PS ℓ} (hf : Ap hℓ B f) : Ap hℓ B (r • f) := by
  intro N
  obtain ⟨I, a, haK, ha, hab⟩ := hf N
  exact ⟨I, r • a, fun i => Submodule.smul_mem _ r (haK i), approx_smul hℓ r ha,
    fun i => Dvd_smul r (hab i)⟩

theorem Ap_mono {B B' : ℕ → ℕ} (h : ∀ i, B' i ≤ B i) {f : PS ℓ} (hf : Ap hℓ B f) : Ap hℓ B' f := by
  intro N
  obtain ⟨I, a, haK, ha, hab⟩ := hf N
  exact ⟨I, a, haK, ha, fun i => Dvd_mono (h i) (hab i)⟩

/-- `ℓ^e·f` gains `e` in every coordinate. -/
theorem Ap_pow_smul {B : ℕ → ℕ} (e : ℕ) {f : PS ℓ} (hf : Ap hℓ B f) :
    Ap hℓ (fun i => B i + e) ((ℓ : ℤ_[ℓ]) ^ e • f) := by
  intro N
  obtain ⟨I, a, haK, ha, hab⟩ := hf N
  refine ⟨I, (ℓ : ℤ_[ℓ]) ^ e • a, fun i => Submodule.smul_mem _ _ (haK i),
    approx_smul hℓ _ ha |> fun h => Dvd_mono (Nat.le_refl N) h, fun i => ?_⟩
  obtain ⟨z, hz⟩ := hab i
  exact ⟨z, by rw [Pi.smul_apply, hz, smul_smul, ← pow_add, add_comm]⟩

/-- a single Katz term. -/
theorem Ap_single {B : ℕ → ℕ} (j : ℕ) {x : Poly ℓ} (hx : x ∈ Kpiece ℓ hℓ j)
    (hB : Dvd (ℓ : ℤ_[ℓ]) (B j) x) : Ap hℓ B (ModP.ev ℤ_[ℓ] x * Einv ℓ hℓ ^ j) := by
  intro N
  classical
  refine ⟨j + 1, fun i => if i = j then x else 0, fun i => ?_, ⟨0, ?_⟩, fun i => ?_⟩
  · dsimp only; split_ifs with h
    · subst h; exact hx
    · exact Submodule.zero_mem _
  · beta_reduce
    rw [Finset.sum_eq_single j (fun i _ hi => by rw [if_neg hi, map_zero, zero_mul])
      (fun h => absurd (Finset.self_mem_range_succ j) h), if_pos rfl, sub_self, smul_zero]
  · dsimp only; split_ifs with h
    · subst h; exact hB
    · exact Dvd_zero _

lemma one_mem_Kpiece : (1 : Poly ℓ) ∈ Kpiece ℓ hℓ 0 := by
  classical
  rw [mem_Kpiece]
  intro d hd
  rw [Finset.mem_coe, ← C_1, support_C, if_neg one_ne_zero, Finset.mem_singleton] at hd
  subst hd
  have := weight_lead hℓ
  refine ⟨by simp, fun ⟨h0, h1⟩ => ?_⟩
  simp only [Finsupp.coe_zero, Pi.zero_apply, nonpos_iff_eq_zero] at h0 h1
  omega

theorem Ap_one {B : ℕ → ℕ} (h0 : B 0 = 0) : Ap hℓ B (1 : PS ℓ) := by
  have := Ap_single (hℓ := hℓ) (B := B) 0 one_mem_Kpiece (by rw [h0]; exact ⟨1, by simp⟩)
  simpa using this

/-- a genuine Katz expansion gives approximations. -/
theorem Ap_of_isKatz {B : ℕ → ℕ} {c : ℕ → Poly ℓ} {f : PS ℓ} (hc : IsKatz ℓ hℓ c f)
    (hB : ∀ i, Dvd (ℓ : ℤ_[ℓ]) (B i) (c i)) : Ap hℓ B f := by
  intro N
  obtain ⟨I, hI⟩ := hc.2 N
  exact ⟨I, c, hc.1, hI I le_rfl, hB⟩

/-- congruence: `Ap` only depends on `f` (rewrite helper). -/
theorem Ap_congr {B : ℕ → ℕ} {f g : PS ℓ} (h : f = g) (hf : Ap hℓ B f) : Ap hℓ B g := h ▸ hf

end DBound
