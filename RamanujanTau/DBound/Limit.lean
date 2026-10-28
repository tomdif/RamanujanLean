import RamanujanTau.DBound.Series

/-!
# From approximate Katz expansions to a genuine Katz expansion

`isKatz_of_Ap`: if `f` has, for every `N`, a finite Katz approximation mod `ℓ^N` with `v_i ≥ B i`
(`Ap B f`), then `f` has a convergent Katz expansion `c` (`IsKatz c f`) with `ℓ^{B i} ∣ c_i`.

* `katz_unique_N`: Katz uniqueness mod `ℓ^N` (iterating `katz_unique_mod`), so the approximants are
  compatible;
* `padic_lim`: `ℤ_ℓ` is `ℓ`-adically complete (Mathlib's `IsAdicComplete (maximalIdeal ℤ_[p])`);
* the limit is taken coefficientwise on the finite monomial set `S(i(ℓ−1))`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace DBound
open MvPolynomial ModP AtkinOBrienFinal AtkinOBrien PowerSeries

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] {hℓ : 5 ≤ ℓ}

lemma map_Dvd_succ {N : ℕ} {g : PS ℓ} (h : Dvd (ℓ : ℤ_[ℓ]) (N + 1) g) :
    PowerSeries.map (PadicInt.toZMod (p := ℓ)) g = 0 := by
  obtain ⟨y, rfl⟩ := h
  rw [PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, map_pow, map_natCast, ZMod.natCast_self,
    zero_pow (Nat.succ_ne_zero N), map_zero, zero_mul]

lemma ksum_smul (I : ℕ) (r : ℤ_[ℓ]) (b : ℕ → Poly ℓ) :
    ksum (hℓ := hℓ) I (fun i => r • b i) = r • ksum (hℓ := hℓ) I b := by
  simp only [ksum, map_smul, smul_mul_assoc, Finset.smul_sum]

/-- **Katz uniqueness mod `ℓ^N`.** -/
theorem katz_unique_N (N : ℕ) : ∀ (I : ℕ) (a : ℕ → Poly ℓ), (∀ i, a i ∈ Kpiece ℓ hℓ i) →
    Dvd (ℓ : ℤ_[ℓ]) N (ksum (hℓ := hℓ) I a) → ∀ i < I, Dvd (ℓ : ℤ_[ℓ]) N (a i) := by
  induction N with
  | zero => intro I a _ _ i _; exact ⟨a i, by rw [pow_zero, one_smul]⟩
  | succ N ih =>
    intro I a ha h i hi
    have hu := katz_unique_mod hℓ ha (map_Dvd_succ h)
    choose! b hb using hu
    set b' : ℕ → Poly ℓ := fun i => if i < I then b i else 0 with hb'
    have hab : ∀ i < I, a i = (ℓ : ℤ_[ℓ]) • b' i := fun i hi => by
      simp only [hb', if_pos hi]; exact hb i hi
    have hb'K : ∀ i, b' i ∈ Kpiece ℓ hℓ i := fun i => by
      by_cases hi : i < I
      · exact Kpiece_of_smul hℓ ell_ne_zero (by rw [← hab i hi]; exact ha i)
      · simp only [hb', if_neg hi]; exact Submodule.zero_mem _
    have he : ksum (hℓ := hℓ) I a = (ℓ : ℤ_[ℓ]) • ksum (hℓ := hℓ) I b' := by
      rw [← ksum_smul]
      exact Finset.sum_congr rfl fun i hi => by rw [hab i (Finset.mem_range.mp hi)]
    obtain ⟨y, hy⟩ := h
    have : ksum (hℓ := hℓ) I b' = (ℓ : ℤ_[ℓ]) ^ N • y := by
      apply smul_cancel PS_reg
      rw [← he, hy, smul_smul, ← pow_succ']
    obtain ⟨z, hz⟩ := ih I b' hb'K ⟨y, this⟩ i hi
    exact ⟨z, by rw [hab i hi, hz, smul_smul, ← pow_succ']⟩

/-- divisibility of a polynomial from divisibility of its coefficients. -/
lemma Poly_Dvd_of_coeff {N : ℕ} (P : Poly ℓ) (h : ∀ d, Dvd (ℓ : ℤ_[ℓ]) N (P.coeff d)) :
    Dvd (ℓ : ℤ_[ℓ]) N P := by
  have hmem : P ∈ Ideal.map (MvPolynomial.C : ℤ_[ℓ] →+* Poly ℓ)
      (Ideal.span {(ℓ : ℤ_[ℓ]) ^ N}) := by
    rw [MvPolynomial.mem_map_C_iff]
    intro m
    obtain ⟨y, hy⟩ := h m
    rw [Ideal.mem_span_singleton']
    exact ⟨y, by rw [hy, smul_eq_mul, mul_comm]⟩
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hmem
  obtain ⟨y, hy⟩ := hmem
  exact ⟨y, by rw [← hy, mul_comm, MvPolynomial.C_mul']⟩

lemma coeff_Dvd {N : ℕ} {P : Poly ℓ} (h : Dvd (ℓ : ℤ_[ℓ]) N P) (d : Fin 2 →₀ ℕ) :
    Dvd (ℓ : ℤ_[ℓ]) N (P.coeff d) := by
  obtain ⟨y, rfl⟩ := h
  exact ⟨y.coeff d, by rw [MvPolynomial.coeff_smul]⟩

lemma Dvd_iff_dvd {N : ℕ} {x : ℤ_[ℓ]} : Dvd (ℓ : ℤ_[ℓ]) N x ↔ (ℓ : ℤ_[ℓ]) ^ N ∣ x := by
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨y, by rw [smul_eq_mul]⟩
  · rintro ⟨y, rfl⟩; exact ⟨y, by rw [smul_eq_mul]⟩

/-- **`ℓ`-adic limits in `ℤ_ℓ`.** -/
theorem padic_lim (x : ℕ → ℤ_[ℓ]) (h : ∀ m n, m ≤ n → Dvd (ℓ : ℤ_[ℓ]) m (x n - x m)) :
    ∃ L : ℤ_[ℓ], ∀ n, Dvd (ℓ : ℤ_[ℓ]) n (L - x n) := by
  have hc : IsPrecomplete (IsLocalRing.maximalIdeal ℤ_[ℓ]) ℤ_[ℓ] := inferInstance
  have key : ∀ (n : ℕ) (z : ℤ_[ℓ]), z ∈ ((IsLocalRing.maximalIdeal ℤ_[ℓ]) ^ n • ⊤ : Ideal ℤ_[ℓ]) ↔
      (ℓ : ℤ_[ℓ]) ^ n ∣ z := by
    intro n z
    rw [smul_eq_mul, Ideal.mul_top, PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  obtain ⟨L, hL⟩ := hc.prec (f := x) (fun {m n} hmn => by
    rw [SModEq.sub_mem, key, ← dvd_neg, neg_sub]
    exact Dvd_iff_dvd.mp (h m n hmn))
  refine ⟨L, fun n => Dvd_iff_dvd.mpr ?_⟩
  have := hL n
  rw [SModEq.sub_mem, key, ← dvd_neg, neg_sub] at this
  exact this

/-- the finite set of monomials of weight `w`. -/
noncomputable def monos (w : ℕ) : Finset (Fin 2 →₀ ℕ) :=
  ((Finset.range (w + 1)) ×ˢ (Finset.range (w + 1))).image
    (fun p => Finsupp.single 0 p.1 + Finsupp.single 1 p.2)

lemma mem_monos {w : ℕ} {s : Fin 2 →₀ ℕ} (h : 4 * s 0 + 6 * s 1 = w) : s ∈ monos w := by
  rw [monos, Finset.mem_image]
  refine ⟨(s 0, s 1), by simp only [Finset.mem_product, Finset.mem_range]; omega, ?_⟩
  ext i; fin_cases i <;> simp

/-- **Approximate Katz expansions with bounds `B` converge to a genuine Katz expansion.** -/
theorem isKatz_of_Ap {B : ℕ → ℕ} {f : PS ℓ} (hf : Ap hℓ B f) :
    ∃ c : ℕ → Poly ℓ, IsKatz ℓ hℓ c f ∧ ∀ i, Dvd (ℓ : ℤ_[ℓ]) (B i) (c i) := by
  classical
  choose I a haK haA haB using hf
  set A : ℕ → ℕ → Poly ℓ := fun N => trunc (I N) (a N) with hA
  have hAK : ∀ N i, A N i ∈ Kpiece ℓ hℓ i := fun N i => trunc_mem hℓ (haK N) i
  have hAB : ∀ N i, Dvd (ℓ : ℤ_[ℓ]) (B i) (A N i) := fun N i => trunc_dvd i (haB N i)
  have hAA : ∀ N J, I N ≤ J → Approx ℓ hℓ N J (A N) f := fun N J hJ => approx_trunc hℓ (haA N) hJ
  -- compatibility
  have hcomp : ∀ N M, N ≤ M → ∀ i, Dvd (ℓ : ℤ_[ℓ]) N (A M i - A N i) := by
    intro N M hNM i
    set J := max (I M) (I N)
    have h1 : Dvd (ℓ : ℤ_[ℓ]) N (f - ksum (hℓ := hℓ) J (A M)) :=
      Dvd_mono hNM (hAA M J (le_max_left _ _))
    have h2 : Dvd (ℓ : ℤ_[ℓ]) N (f - ksum (hℓ := hℓ) J (A N)) := hAA N J (le_max_right _ _)
    have h3 : Dvd (ℓ : ℤ_[ℓ]) N (ksum (hℓ := hℓ) J (fun i => A M i - A N i)) := by
      have : ksum (hℓ := hℓ) J (fun i => A M i - A N i) =
          (f - ksum (hℓ := hℓ) J (A N)) - (f - ksum (hℓ := hℓ) J (A M)) := by
        simp only [ksum, map_sub, sub_mul, Finset.sum_sub_distrib]; abel
      rw [this, sub_eq_add_neg, ← neg_one_smul ℤ_[ℓ] (f - ksum J (A M))]
      exact Dvd_add h2 (Dvd_smul _ h1)
    by_cases hi : i < J
    · exact katz_unique_N N J _ (fun i => Submodule.sub_mem _ (hAK M i) (hAK N i)) h3 i hi
    · have e1 : A M i = 0 := by simp only [hA, AtkinOBrienFinal.trunc]; rw [if_neg (by omega)]
      have e2 : A N i = 0 := by simp only [hA, AtkinOBrienFinal.trunc]; rw [if_neg (by omega)]
      rw [e1, e2, sub_zero]; exact Dvd_zero _
  -- coefficientwise limits
  have hlim : ∀ i d, ∃ L : ℤ_[ℓ], ∀ n, Dvd (ℓ : ℤ_[ℓ]) n (L - (A n i).coeff d) := fun i d =>
    padic_lim (fun n => (A n i).coeff d) fun m n hmn => by
      rw [← coeff_sub]; exact coeff_Dvd (hcomp m n hmn i) d
  choose L hL using hlim
  set c : ℕ → Poly ℓ := fun i => ∑ d ∈ monos (i * (ℓ - 1)),
    monomial d (if d ∈ Igusa.S ℓ hℓ (i * (ℓ - 1)) then L i d else 0) with hc
  have hcoeff : ∀ i d, (c i).coeff d = if d ∈ Igusa.S ℓ hℓ (i * (ℓ - 1)) then L i d else 0 := by
    intro i d
    simp only [hc, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    by_cases hS : d ∈ Igusa.S ℓ hℓ (i * (ℓ - 1))
    · rw [if_pos (mem_monos hS.1)]
    · rw [if_neg hS]; split_ifs <;> rfl
  have hcK : ∀ i, c i ∈ Kpiece ℓ hℓ i := fun i => by
    rw [mem_Kpiece]
    intro d hd
    rw [Finset.mem_coe, mem_support_iff, hcoeff] at hd
    by_contra hS
    exact hd (if_neg hS)
  have hkey : ∀ N i, Dvd (ℓ : ℤ_[ℓ]) N (c i - A N i) := by
    intro N i
    refine Poly_Dvd_of_coeff _ fun d => ?_
    rw [coeff_sub, hcoeff]
    split_ifs with hS
    · exact hL i d N
    · have : (A N i).coeff d = 0 := by
        by_contra h0
        exact hS ((mem_Kpiece hℓ).mp (hAK N i) (mem_support_iff.mpr h0))
      rw [this, sub_zero]; exact Dvd_zero _
  have hev : ∀ {N : ℕ} {P : Poly ℓ} (g : PS ℓ), Dvd (ℓ : ℤ_[ℓ]) N P →
      Dvd (ℓ : ℤ_[ℓ]) N (ModP.ev ℤ_[ℓ] P * g) := by
    rintro N P g ⟨y, rfl⟩
    exact ⟨ModP.ev ℤ_[ℓ] y * g, by rw [map_smul, smul_mul_assoc]⟩
  refine ⟨c, ⟨hcK, fun N => ⟨I N, fun I' hI' => ?_⟩⟩, fun i => ?_⟩
  · have h1 : Dvd (ℓ : ℤ_[ℓ]) N (f - ksum (hℓ := hℓ) I' (A N)) := hAA N I' hI'
    have h2 : Dvd (ℓ : ℤ_[ℓ]) N (ksum (hℓ := hℓ) I' (fun i => A N i - c i)) := by
      refine Dvd.sum _ _ fun i _ => hev _ ?_
      have := Dvd_smul (-1 : ℤ_[ℓ]) (hkey N i)
      rwa [neg_one_smul, neg_sub] at this
    have := Dvd_add h1 h2
    have e : f - ksum (hℓ := hℓ) I' (A N) + ksum (hℓ := hℓ) I' (fun i => A N i - c i) =
        f - ∑ i ∈ Finset.range I', ModP.ev ℤ_[ℓ] (c i) * Einv ℓ hℓ ^ i := by
      simp only [ksum, map_sub, sub_mul, Finset.sum_sub_distrib]; abel
    unfold Approx
    rwa [e] at this
  · have := Dvd_add (hkey (B i) i) (hAB (B i) i)
    rwa [sub_add_cancel] at this

end DBound
