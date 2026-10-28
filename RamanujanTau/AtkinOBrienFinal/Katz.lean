import RamanujanTau.Igusa.Complement
import RamanujanTau.TateCurve.Hasse
import RamanujanTau.AtkinOBrien.Induction

/-!
# Katz expansions over `ℤ_ℓ`, concretely

Throughout `ℓ ≥ 5` is prime, `E = E_{ℓ−1} ∈ ℤ_ℓ⟦q⟧` (`TateCurve.EhasseZp`) and `E⁻¹` its inverse
(`E ≡ 1 mod ℓ`, so `E` is a unit).

* **Katz pieces.** `Kpiece i ⊆ ℤ_ℓ[X₀, X₁]` is the `ℤ_ℓ`-span of the monomials in `Igusa.S ℓ (i(ℓ−1))`
  (weight `i(ℓ−1)` monomials not divisible by the leading monomial of `Ā`). `X₀, X₁ ↦ E₄, E₆` (`ModP.ev`)
  sends it into `M_{i(ℓ−1)}(ℤ_ℓ)`; it is the monomial complement `B_i` of `E·M_{(i−1)(ℓ−1)}`.
  Katz coordinates of `b ∈ B_i` are the coefficients of its polynomial; `v_i(b) ≥ m` is
  `AtkinOBrien.Dvd ℓ m b` in `ℤ_ℓ[X₀, X₁]`.
* **`Approx N I a f`**: `f ≡ Σ_{i<I} a_i(E₄,E₆)/E^i (mod ℓ^N)` in `ℤ_ℓ⟦q⟧`.
* **`IsKatz a f`**: `a_i ∈ B_i` and `Σ_i a_i/E^i → f` ℓ-adically (partial sums eventually agree with `f`
  mod every `ℓ^N`): `a` is a Katz expansion of `f`.
* **`Env c γ f`**: `f` is, modulo every `ℓ^N`, a finite Katz series with `v_i ≥ max(0, γ(i) − c)`, i.e. `f`
  lies in the closure of the envelope `A_c(γ)` of `docs/ATKIN_OBRIEN_PROOF.md`, Step 2.
* **`env_div`** (Katz uniqueness mod `ℓ`, from `Igusa.katz_independent_S`): if `f ∈ Env c γ` and
  `f = ℓ y`, then `y ∈ Env (c+1) γ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AtkinOBrienFinal
open PowerSeries AtkinOBrien

variable (ℓ : ℕ) [hℓp : Fact ℓ.Prime] (hℓ : 5 ≤ ℓ)

/-- `ℤ_ℓ[X₀, X₁]` (`X₀ ↦ E₄`, `X₁ ↦ E₆`). -/
abbrev Poly := MvPolynomial (Fin 2) ℤ_[ℓ]

/-- `ℤ_ℓ⟦q⟧`. -/
abbrev PS := PowerSeries ℤ_[ℓ]

/-- **The Katz piece `B_i`**: polynomials supported on the monomial complement `S(i(ℓ−1))`. -/
noncomputable def Kpiece (i : ℕ) : Submodule ℤ_[ℓ] (Poly ℓ) :=
  MvPolynomial.restrictSupport ℤ_[ℓ] (Igusa.S ℓ hℓ (i * (ℓ - 1)))

/-- `E = E_{ℓ−1} ∈ ℤ_ℓ⟦q⟧`. -/
noncomputable def E : PS ℓ := TateCurve.EhasseZp ℓ (le_trans (by norm_num) hℓ)

lemma map_E : PowerSeries.map (PadicInt.toZMod (p := ℓ)) (E ℓ hℓ) = 1 :=
  TateCurve.map_toZMod_EhasseZp _

lemma isUnit_const_E : IsUnit (constantCoeff (E ℓ hℓ)) := by
  have h : PadicInt.toZMod (constantCoeff (E ℓ hℓ)) = 1 := by
    have := congrArg constantCoeff (map_E ℓ hℓ)
    rwa [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      map_one] at this
  by_contra hu
  have hm : constantCoeff (E ℓ hℓ) ∈ IsLocalRing.maximalIdeal ℤ_[ℓ] :=
    (IsLocalRing.mem_maximalIdeal _).mpr hu
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker, h] at hm
  exact one_ne_zero hm

/-- `E⁻¹ ∈ ℤ_ℓ⟦q⟧`. -/
noncomputable def Einv : PS ℓ := (E ℓ hℓ).invOfUnit (isUnit_const_E ℓ hℓ).unit

lemma E_mul_Einv : E ℓ hℓ * Einv ℓ hℓ = 1 := PowerSeries.mul_invOfUnit _ _ rfl

lemma map_Einv : PowerSeries.map (PadicInt.toZMod (p := ℓ)) (Einv ℓ hℓ) = 1 := by
  have := congrArg (PowerSeries.map (PadicInt.toZMod (p := ℓ))) (E_mul_Einv ℓ hℓ)
  rwa [map_mul, map_E, one_mul, map_one] at this

/-- the reduction of `Σ_{i<I} a_i/E^i` mod `ℓ`. -/
lemma map_katzSum (I : ℕ) (a : ℕ → Poly ℓ) :
    PowerSeries.map (PadicInt.toZMod (p := ℓ))
        (∑ i ∈ Finset.range I, ModP.ev ℤ_[ℓ] (a i) * Einv ℓ hℓ ^ i) =
      ∑ i ∈ Finset.range I, ModP.ev (ZMod ℓ) (MvPolynomial.map (PadicInt.toZMod (p := ℓ)) (a i)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, map_Einv, one_pow, mul_one, ModP.map_ev]

/-- `f ≡ Σ_{i<I} a_i(E₄,E₆)/E^i (mod ℓ^N)`. -/
def Approx (N I : ℕ) (a : ℕ → Poly ℓ) (f : PS ℓ) : Prop :=
  Dvd (ℓ : ℤ_[ℓ]) N (f - ∑ i ∈ Finset.range I, ModP.ev ℤ_[ℓ] (a i) * Einv ℓ hℓ ^ i)

/-- **`a` is a Katz expansion of `f`**: `a_i ∈ B_i` and `Σ_i a_i/E^i` converges ℓ-adically to `f`. -/
def IsKatz (a : ℕ → Poly ℓ) (f : PS ℓ) : Prop :=
  (∀ i, a i ∈ Kpiece ℓ hℓ i) ∧ ∀ N, ∃ I, ∀ I', I ≤ I' → Approx ℓ hℓ N I' a f

/-- **The envelope `A_c(γ)` (closure form)**: for every `N`, `f` is congruent mod `ℓ^N` to a finite Katz
series with `v_i ≥ max(0, γ(i) − c)`. -/
def Env (c : ℤ) (γ : ℕ → ℤ) (f : PS ℓ) : Prop :=
  ∀ N, ∃ I, ∃ a : ℕ → Poly ℓ, (∀ i, a i ∈ Kpiece ℓ hℓ i) ∧ Approx ℓ hℓ N I a f ∧
    ∀ i, Dvd (ℓ : ℤ_[ℓ]) (max 0 (γ i - c)).toNat (a i)

/-! ### basic algebra -/

variable {ℓ}

lemma ell_ne_zero : (ℓ : ℤ_[ℓ]) ≠ 0 := Nat.cast_ne_zero.mpr hℓp.out.ne_zero

lemma PS_reg (x : PS ℓ) (h : (ℓ : ℤ_[ℓ]) • x = 0) : x = 0 := by
  ext n
  have := congrArg (coeff n) h
  rw [coeff_smul, map_zero, smul_eq_mul] at this
  exact (mul_eq_zero.mp this).resolve_left ell_ne_zero

lemma Poly_reg (x : Poly ℓ) (h : (ℓ : ℤ_[ℓ]) • x = 0) : x = 0 := by
  ext d
  have := congrArg (MvPolynomial.coeff d) h
  rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_zero, smul_eq_mul] at this
  rw [MvPolynomial.coeff_zero]
  exact (mul_eq_zero.mp this).resolve_left ell_ne_zero

lemma smul_cancel {M : Type*} [AddCommGroup M] [Module ℤ_[ℓ] M]
    (hreg : ∀ x : M, (ℓ : ℤ_[ℓ]) • x = 0 → x = 0) {x y : M} (h : (ℓ : ℤ_[ℓ]) • x = (ℓ : ℤ_[ℓ]) • y) :
    x = y :=
  sub_eq_zero.mp (hreg _ (by rw [smul_sub, h, sub_self]))

/-- divisibility by `ℓ` of a power series from vanishing mod `ℓ`. -/
lemma PS_dvd_of_map (g : PS ℓ) (h : PowerSeries.map (PadicInt.toZMod (p := ℓ)) g = 0) :
    ∃ y : PS ℓ, g = (ℓ : ℤ_[ℓ]) • y := by
  have hc : ∀ n, ∃ z : ℤ_[ℓ], coeff n g = ℓ * z := by
    intro n
    have h1 := congrArg (coeff n) h
    rw [coeff_map, map_zero] at h1
    have : coeff n g ∈ IsLocalRing.maximalIdeal ℤ_[ℓ] := by
      rw [← PadicInt.ker_toZMod]; exact h1
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at this
    obtain ⟨z, hz⟩ := this
    exact ⟨z, by rw [← hz, mul_comm]⟩
  choose z hz using hc
  refine ⟨PowerSeries.mk z, ?_⟩
  ext n
  rw [coeff_smul, coeff_mk, smul_eq_mul, hz]

/-- divisibility by `ℓ` of a polynomial from vanishing mod `ℓ`. -/
lemma Poly_dvd_of_map (P : Poly ℓ) (h : MvPolynomial.map (PadicInt.toZMod (p := ℓ)) P = 0) :
    ∃ y : Poly ℓ, P = (ℓ : ℤ_[ℓ]) • y := by
  have hmem : P ∈ Ideal.map (MvPolynomial.C : ℤ_[ℓ] →+* Poly ℓ) (IsLocalRing.maximalIdeal ℤ_[ℓ]) := by
    rw [MvPolynomial.mem_map_C_iff]
    intro m
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, ← MvPolynomial.coeff_map, h, MvPolynomial.coeff_zero]
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton'] at hmem
  obtain ⟨y, hy⟩ := hmem
  exact ⟨y, by rw [← hy, mul_comm, MvPolynomial.C_mul']⟩

lemma mem_Kpiece {i : ℕ} {P : Poly ℓ} :
    P ∈ Kpiece ℓ hℓ i ↔ (P.support : Set (Fin 2 →₀ ℕ)) ⊆ Igusa.S ℓ hℓ (i * (ℓ - 1)) :=
  MvPolynomial.mem_restrictSupport_iff _

lemma Kpiece_of_smul {i : ℕ} {y : Poly ℓ} {r : ℤ_[ℓ]} (hr : r ≠ 0) (h : r • y ∈ Kpiece ℓ hℓ i) :
    y ∈ Kpiece ℓ hℓ i := by
  rw [Kpiece, MvPolynomial.mem_restrictSupport_iff] at h ⊢
  rwa [MvPolynomial.support_smul_eq hr] at h

lemma Dvd_zero (N : ℕ) {M : Type*} [AddCommGroup M] [Module ℤ_[ℓ] M] : Dvd (ℓ : ℤ_[ℓ]) N (0 : M) :=
  ⟨0, by rw [smul_zero]⟩

lemma Dvd_add {N : ℕ} {M : Type*} [AddCommGroup M] [Module ℤ_[ℓ] M] {x y : M}
    (hx : Dvd (ℓ : ℤ_[ℓ]) N x) (hy : Dvd (ℓ : ℤ_[ℓ]) N y) : Dvd (ℓ : ℤ_[ℓ]) N (x + y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a + b, by rw [smul_add]⟩

lemma Dvd_smul {N : ℕ} {M : Type*} [AddCommGroup M] [Module ℤ_[ℓ] M] (r : ℤ_[ℓ]) {x : M}
    (hx : Dvd (ℓ : ℤ_[ℓ]) N x) : Dvd (ℓ : ℤ_[ℓ]) N (r • x) := by
  obtain ⟨a, rfl⟩ := hx; exact ⟨r • a, by rw [smul_comm]⟩

lemma Dvd_mono {M : Type*} [AddCommGroup M] [Module ℤ_[ℓ] M] {a b : ℕ} {x : M} (hab : a ≤ b)
    (h : Dvd (ℓ : ℤ_[ℓ]) b x) : Dvd (ℓ : ℤ_[ℓ]) a x := by
  obtain ⟨y, rfl⟩ := h
  exact ⟨(ℓ : ℤ_[ℓ]) ^ (b - a) • y, by rw [← mul_smul, ← pow_add, Nat.add_sub_cancel' hab]⟩

/-- zero-extension of a coefficient sequence past `I`. -/
noncomputable def trunc (I : ℕ) (a : ℕ → Poly ℓ) : ℕ → Poly ℓ := fun i => if i < I then a i else 0

lemma approx_trunc {N I I' : ℕ} {a : ℕ → Poly ℓ} {f : PS ℓ} (h : Approx ℓ hℓ N I a f) (hI : I ≤ I') :
    Approx ℓ hℓ N I' (trunc I a) f := by
  have : ∑ i ∈ Finset.range I', ModP.ev ℤ_[ℓ] (trunc I a i) * Einv ℓ hℓ ^ i =
      ∑ i ∈ Finset.range I, ModP.ev ℤ_[ℓ] (a i) * Einv ℓ hℓ ^ i := by
    rw [← Finset.sum_range_add_sum_Ico _ hI]
    rw [Finset.sum_eq_zero (s := Finset.Ico I I') (fun i hi => by
      rw [trunc, if_neg (by simp at hi; omega), map_zero, zero_mul]), add_zero]
    exact Finset.sum_congr rfl fun i hi => by rw [trunc, if_pos (Finset.mem_range.mp hi)]
  unfold Approx; rw [this]; exact h

lemma trunc_mem {I : ℕ} {a : ℕ → Poly ℓ} (h : ∀ i, a i ∈ Kpiece ℓ hℓ i) (i : ℕ) :
    trunc I a i ∈ Kpiece ℓ hℓ i := by
  unfold trunc; split_ifs
  · exact h i
  · exact Submodule.zero_mem _

lemma trunc_dvd {I m : ℕ} {a : ℕ → Poly ℓ} (i : ℕ) (h : Dvd (ℓ : ℤ_[ℓ]) m (a i)) :
    Dvd (ℓ : ℤ_[ℓ]) m (trunc I a i) := by
  unfold trunc; split_ifs
  · exact h
  · exact Dvd_zero m

lemma approx_add {N I : ℕ} {a b : ℕ → Poly ℓ} {f g : PS ℓ} (ha : Approx ℓ hℓ N I a f)
    (hb : Approx ℓ hℓ N I b g) : Approx ℓ hℓ N I (a + b) (f + g) := by
  unfold Approx at *
  have : f + g - ∑ i ∈ Finset.range I, ModP.ev ℤ_[ℓ] ((a + b) i) * Einv ℓ hℓ ^ i =
      (f - ∑ i ∈ Finset.range I, ModP.ev ℤ_[ℓ] (a i) * Einv ℓ hℓ ^ i) +
        (g - ∑ i ∈ Finset.range I, ModP.ev ℤ_[ℓ] (b i) * Einv ℓ hℓ ^ i) := by
    simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]; abel
  rw [this]; exact Dvd_add ha hb

lemma approx_smul {N I : ℕ} (r : ℤ_[ℓ]) {a : ℕ → Poly ℓ} {f : PS ℓ} (ha : Approx ℓ hℓ N I a f) :
    Approx ℓ hℓ N I (r • a) (r • f) := by
  unfold Approx at *
  have : r • f - ∑ i ∈ Finset.range I, ModP.ev ℤ_[ℓ] ((r • a) i) * Einv ℓ hℓ ^ i =
      r • (f - ∑ i ∈ Finset.range I, ModP.ev ℤ_[ℓ] (a i) * Einv ℓ hℓ ^ i) := by
    simp only [Pi.smul_apply, map_smul, smul_mul_assoc, smul_sub, Finset.smul_sum]
  rw [this]; exact Dvd_smul r ha

/-- **The envelope as a submodule** (with the cusp condition `coeff 0 = 0`). -/
def envSub (c : ℤ) (γ : ℕ → ℤ) : Submodule ℤ_[ℓ] (PS ℓ) where
  carrier := {f | coeff 0 f = 0 ∧ Env ℓ hℓ c γ f}
  zero_mem' := by
    refine ⟨by simp, fun N => ⟨0, 0, fun i => Submodule.zero_mem _, ?_, fun i => Dvd_zero _⟩⟩
    exact ⟨0, by simp⟩
  add_mem' := by
    rintro f g ⟨hf0, hf⟩ ⟨hg0, hg⟩
    refine ⟨by rw [map_add, hf0, hg0, add_zero], fun N => ?_⟩
    obtain ⟨I₁, a, haK, ha, hab⟩ := hf N
    obtain ⟨I₂, b, hbK, hb, hbb⟩ := hg N
    refine ⟨max I₁ I₂, trunc I₁ a + trunc I₂ b, fun i => Submodule.add_mem _ (trunc_mem hℓ haK i)
      (trunc_mem hℓ hbK i), approx_add hℓ (approx_trunc hℓ ha (le_max_left _ _))
      (approx_trunc hℓ hb (le_max_right _ _)), fun i => Dvd_add (trunc_dvd i (hab i)) (trunc_dvd i (hbb i))⟩
  smul_mem' := by
    rintro r f ⟨hf0, hf⟩
    refine ⟨by rw [coeff_smul, hf0, smul_zero], fun N => ?_⟩
    obtain ⟨I, a, haK, ha, hab⟩ := hf N
    exact ⟨I, r • a, fun i => Submodule.smul_mem _ r (haK i), approx_smul hℓ r ha,
      fun i => Dvd_smul r (hab i)⟩

/-! ### Katz uniqueness mod `ℓ` -/

lemma iso_of_mem {i : ℕ} {P : MvPolynomial (Fin 2) (ZMod ℓ)}
    (h : (P.support : Set (Fin 2 →₀ ℕ)) ⊆ Igusa.S ℓ hℓ (i * (ℓ - 1))) : ModP.Iso P (0 + i * (ℓ - 1)) := by
  intro d hd
  have := (h (MvPolynomial.mem_support_iff.mpr hd)).1
  rw [ModP.weight_wt, zero_add]; exact this

/-- **Katz uniqueness mod `ℓ`**: a finite Katz series `≡ 0 (mod ℓ)` has all coordinates `≡ 0 (mod ℓ)`. -/
theorem katz_unique_mod {I : ℕ} {a : ℕ → Poly ℓ} (ha : ∀ i, a i ∈ Kpiece ℓ hℓ i)
    (h : PowerSeries.map (PadicInt.toZMod (p := ℓ))
      (∑ i ∈ Finset.range I, ModP.ev ℤ_[ℓ] (a i) * Einv ℓ hℓ ^ i) = 0) :
    ∀ i < I, ∃ b : Poly ℓ, a i = (ℓ : ℤ_[ℓ]) • b := by
  intro i hi
  apply Poly_dvd_of_map
  obtain ⟨n, rfl⟩ : ∃ n, I = n + 1 := ⟨I - 1, by omega⟩
  rw [map_katzSum] at h
  refine Igusa.katz_independent_S hℓ 0 n (fun i => MvPolynomial.map (PadicInt.toZMod (p := ℓ)) (a i))
    (fun j _ => iso_of_mem hℓ ?_) (fun j _ => ?_) h i (by omega)
  · exact (Finset.coe_subset.mpr (MvPolynomial.support_map_subset _ _)).trans
      ((mem_Kpiece hℓ).mp (ha j))
  · rw [zero_add]
    exact (Finset.coe_subset.mpr (MvPolynomial.support_map_subset _ _)).trans
      ((mem_Kpiece hℓ).mp (ha j))

/-- **`hdiv` at the envelope level**: if `f ∈ Env c γ` and `f = ℓ y` then `y ∈ Env (c+1) γ`. -/
theorem env_div (c : ℤ) (γ : ℕ → ℤ) {f y : PS ℓ} (hf : Env ℓ hℓ c γ f) (hfy : f = (ℓ : ℤ_[ℓ]) • y) :
    Env ℓ hℓ (c + 1) γ y := by
  intro N
  obtain ⟨I, a, haK, ⟨g, hg⟩, hab⟩ := hf (N + 1)
  have hmap : PowerSeries.map (PadicInt.toZMod (p := ℓ))
      (∑ i ∈ Finset.range I, ModP.ev ℤ_[ℓ] (a i) * Einv ℓ hℓ ^ i) = 0 := by
    have e : ∑ i ∈ Finset.range I, ModP.ev ℤ_[ℓ] (a i) * Einv ℓ hℓ ^ i =
        (ℓ : ℤ_[ℓ]) • (y - (ℓ : ℤ_[ℓ]) ^ N • g) := by
      rw [smul_sub, ← hfy, smul_smul, ← pow_succ', ← hg]; abel
    rw [e, PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, map_natCast, ZMod.natCast_self,
      map_zero, zero_mul]
  have hu := katz_unique_mod hℓ haK hmap
  choose! b hb using hu
  set b' : ℕ → Poly ℓ := fun i => if i < I then b i else 0 with hb'
  have hab' : ∀ i < I, a i = (ℓ : ℤ_[ℓ]) • b' i := fun i hi => by simp only [hb', if_pos hi]; exact hb i hi
  refine ⟨I, b', fun i => ?_, ⟨g, ?_⟩, fun i => ?_⟩
  · by_cases hi : i < I
    · exact Kpiece_of_smul hℓ ell_ne_zero (by rw [← hab' i hi]; exact haK i)
    · simp only [hb', if_neg hi]; exact Submodule.zero_mem _
  · apply smul_cancel PS_reg
    rw [smul_smul, ← pow_succ', ← hg, hfy, smul_sub, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hab' i (Finset.mem_range.mp hi), map_smul, smul_mul_assoc]
  · by_cases hi : i < I
    · obtain ⟨z, hz⟩ := hab i
      set e := (max 0 (γ i - c)).toNat with he
      rcases Nat.eq_zero_or_pos e with h0 | hpos
      · have : (max 0 (γ i - (c + 1))).toNat = 0 := by omega
        rw [this]; exact ⟨b' i, by rw [pow_zero, one_smul]⟩
      · refine Dvd_mono (b := e - 1) (by omega) ⟨z, ?_⟩
        apply smul_cancel Poly_reg
        rw [← hab' i hi, hz, smul_smul, ← pow_succ', Nat.sub_add_cancel hpos]
    · simp only [hb', if_neg hi]; exact Dvd_zero _

end AtkinOBrienFinal
