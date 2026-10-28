/-
# The Hasse invariant as an isobaric polynomial in `c₄, c₆` (characteristic `p ≥ 5`)

* `hasseH_eq_coeff_fpoly`: `H(W)` is the coefficient of `x^{p−1}` in `f(x)^{(p−1)/2}`,
  `f = 4x³ + b₂x² + 2b₄x + b₆` (dehomogenization of `hasseH`).
* `coeff_comp_shift`: in characteristic `p`, the coefficient of `x^{p−1}` of a polynomial of degree
  `≤ 2p − 2` does not change under `x ↦ x + r` (`p ∣ C(p−1+i, p−1)` for `1 ≤ i ≤ p − 1`).
* `hassePoly p ∈ 𝔽_p[X₀, X₁]`: the coefficient of `x^{p−1}` in `(4x³ − (X₀/12) x + 8 X₁/12³)^{(p−1)/2}`;
  `iso_hassePoly`: isobaric of weight `p − 1` for the weights `(4, 6)`;
  `eval_hassePoly`: for every Weierstrass curve over a ring of characteristic `p`,
  `hassePoly(c₄, −c₆) = H(W)` (completing the cube `x ↦ x − b₂/12`, which needs `p ≥ 5`).
* `aH_formalGroup_eq_hassePoly`: hence `a = hassePoly(c₄, −c₆)` for the formal group of `W`.
-/
import RamanujanTau.HasseInv.Elliptic
import RamanujanTau.ModP.SwinnertonDyer

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace HasseInv
open Polynomial

variable {R : Type*} [CommRing R]

/-- `f(x) = 4x³ + b₂x² + 2b₄x + b₆ = (2y + a₁x + a₃)²`. -/
noncomputable def fpoly (W : WeierstrassCurve R) : R[X] :=
  C 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆

lemma natDegree_fpoly (W : WeierstrassCurve R) : (fpoly W).natDegree ≤ 3 := natDegree_cubic_le

lemma aeval_fhat (W : WeierstrassCurve R) :
    MvPolynomial.aeval (![X, 1] : Fin 2 → R[X]) (fhat W) = fpoly W := by
  simp [fhat, fpoly, Polynomial.algebraMap_apply, map_ofNat]

/-- dehomogenization: for `P` homogeneous of degree `n` and `k ≤ n`, the coefficient of `x^k` in
`P(x, 1)` is the coefficient of `X^k Y^{n−k}` in `P`. -/
lemma coeff_dehom (P : MvPolynomial (Fin 2) R) {n k : ℕ} (hP : P.IsHomogeneous n) (hk : k ≤ n) :
    (MvPolynomial.aeval (![X, 1] : Fin 2 → R[X]) P).coeff k =
      P.coeff (Finsupp.single 0 k + Finsupp.single 1 (n - k)) := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', finsetSum_coeff]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, mul_one,
    Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, coeff_C_mul_X_pow]
  set d₀ : Fin 2 →₀ ℕ := Finsupp.single 0 k + Finsupp.single 1 (n - k) with hd₀
  have hdeg : ∀ d : Fin 2 →₀ ℕ, d ∈ P.support → d 0 + d 1 = n := by
    intro d hdm
    have := hP (MvPolynomial.mem_support_iff.mp hdm)
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at this
    simpa using this
  rw [Finset.sum_eq_single d₀]
  · rw [if_pos (by simp [hd₀])]
  · intro d hdm hne
    rw [if_neg]
    intro h0
    apply hne
    ext i; fin_cases i
    · simp [hd₀, h0]
    · have := hdeg d hdm; simp [hd₀]; omega
  · intro hn
    rw [MvPolynomial.notMem_support_iff.mp hn, ite_self]

/-- **`H(W)` = coefficient of `x^{p−1}` in `f(x)^{(p−1)/2}`** (`p` odd). -/
theorem hasseH_eq_coeff_fpoly (p : ℕ) (hp : p % 2 = 1) (W : WeierstrassCurve R) :
    hasseH p W = (fpoly W ^ ((p - 1) / 2)).coeff (p - 1) := by
  rw [hasseH, ← aeval_fhat, ← map_pow,
    coeff_dehom _ ((fhat_isHomogeneous W).pow ((p - 1) / 2)) (by omega)]
  congr 3
  omega

section CharP
variable (p : ℕ) [hp : Fact p.Prime] [CharP R p]

/-- in characteristic `p`, `x ↦ x + r` does not change the coefficient of `x^{p−1}` of a polynomial of
degree `≤ 2p − 2`. -/
lemma coeff_comp_shift (g : R[X]) (hg : g.natDegree ≤ 2 * p - 2) (r : R) :
    (g.comp (X + C r)).coeff (p - 1) = g.coeff (p - 1) := by
  have h1p := hp.out.one_lt
  rw [← taylor_apply, taylor_coeff, eval_eq_sum_range' (n := p)]
  · rw [Finset.sum_eq_single 0]
    · simp [hasseDeriv_coeff]
    · intro i hi hi0
      rw [hasseDeriv_coeff]
      have hd : p ∣ (i + (p - 1)).choose (p - 1) := by
        rw [add_comm]
        exact Nat.Prime.dvd_choose_add hp.out (by omega) (Finset.mem_range.mp hi) (by omega)
      obtain ⟨c, hc⟩ := hd
      rw [hc]; push_cast; rw [CharP.cast_eq_zero]; ring
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · calc (hasseDeriv (p - 1) g).natDegree ≤ g.natDegree - (p - 1) := natDegree_hasseDeriv_le _ _
      _ < p := by omega

end CharP

/-! ## The polynomial `hassePoly ∈ 𝔽_p[X₀, X₁]` -/

section Hasse
variable (p : ℕ) [hp : Fact p.Prime]

local notation "A" => MvPolynomial (Fin 2) (ZMod p)

/-- `1/12 ∈ 𝔽_p`. -/
noncomputable def u12 : ZMod p := (12 : ZMod p)⁻¹

/-- `g(x) = 4x³ − (X₀/12) x + 8X₁/12³ ∈ 𝔽_p[X₀,X₁][x]`; for `(X₀, X₁) = (c₄, −c₆)` this is
`f(x − b₂/12) = 4x³ − (c₄/12) x − c₆/216`. -/
noncomputable def gpoly : A[X] :=
  C 4 * X ^ 3 - C (MvPolynomial.C (u12 p) * MvPolynomial.X 0) * X +
    C (MvPolynomial.C (8 * u12 p ^ 3) * MvPolynomial.X 1)

/-- **the Hasse polynomial** `coeff_{x^{p−1}} g(x)^{(p−1)/2} ∈ 𝔽_p[X₀,X₁]`. -/
noncomputable def hassePoly : A := (gpoly p ^ ((p - 1) / 2)).coeff (p - 1)

/-- coefficients of `P ∈ A[x]` are isobaric with `wt(xʲ · coeff) = α`. -/
def Good (P : A[X]) (α : ℕ) : Prop :=
  ∀ j, ModP.Iso (P.coeff j) (α - 2 * j) ∧ (α < 2 * j → P.coeff j = 0)

lemma good_one : Good p 1 0 := by
  intro j
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp only [coeff_one_zero]
    exact ⟨MvPolynomial.isWeightedHomogeneous_one _ _, fun h => absurd h (by omega)⟩
  · rw [coeff_one, if_neg (by omega)]
    exact ⟨MvPolynomial.isWeightedHomogeneous_zero _ _ _, fun _ => rfl⟩

lemma good_mul {P Q : A[X]} {α β : ℕ} (hP : Good p P α) (hQ : Good p Q β) : Good p (P * Q) (α + β) := by
  intro k
  rw [coeff_mul]
  constructor
  · refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun x hx => ?_
    have hx' := Finset.mem_antidiagonal.mp hx
    by_cases h1 : α < 2 * x.1
    · rw [(hP x.1).2 h1, zero_mul]; exact MvPolynomial.isWeightedHomogeneous_zero _ _ _
    by_cases h2 : β < 2 * x.2
    · rw [(hQ x.2).2 h2, mul_zero]; exact MvPolynomial.isWeightedHomogeneous_zero _ _ _
    exact ModP.iso_of_eq ((hP x.1).1.mul (hQ x.2).1) (by omega)
  · intro hk
    refine Finset.sum_eq_zero fun x hx => ?_
    have hx' := Finset.mem_antidiagonal.mp hx
    by_cases h1 : α < 2 * x.1
    · rw [(hP x.1).2 h1, zero_mul]
    · rw [(hQ x.2).2 (by omega), mul_zero]

lemma good_pow {P : A[X]} {α : ℕ} (hP : Good p P α) (n : ℕ) : Good p (P ^ n) (n * α) := by
  induction n with
  | zero => simpa using good_one p
  | succ n ih => rw [pow_succ, show (n + 1) * α = n * α + α by ring]; exact good_mul p ih hP

lemma good_gpoly : Good p (gpoly p) 6 := by
  have hC : ∀ r : ZMod p, ModP.Iso (MvPolynomial.C r : A) 0 := fun r =>
    MvPolynomial.isWeightedHomogeneous_C _ _
  have hX0 : ModP.Iso (MvPolynomial.X 0 : A) 4 := MvPolynomial.isWeightedHomogeneous_X _ _ 0
  have hX1 : ModP.Iso (MvPolynomial.X 1 : A) 6 := MvPolynomial.isWeightedHomogeneous_X _ _ 1
  have h0 := MvPolynomial.isWeightedHomogeneous_zero (ZMod p) ModP.wt
  intro j
  have e : (gpoly p).coeff j = (if j = 3 then (4 : A) else 0) -
      (if j = 1 then MvPolynomial.C (u12 p) * MvPolynomial.X 0 else 0) +
      (if j = 0 then MvPolynomial.C (8 * u12 p ^ 3) * MvPolynomial.X 1 else 0) := by
    simp only [gpoly, coeff_add, coeff_sub, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  rw [e]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ 4 ≤ j by omega) with rfl | rfl | rfl | rfl | hj
  · simp only [if_true, show (0 : ℕ) ≠ 3 by decide, show (0 : ℕ) ≠ 1 by decide, if_false, sub_zero,
      zero_add]
    exact ⟨ModP.iso_of_eq ((hC _).mul hX1) (by norm_num), fun h => absurd h (by omega)⟩
  · simp only [if_true, show (1 : ℕ) ≠ 3 by decide, show (1 : ℕ) ≠ 0 by decide, if_false, zero_sub,
      add_zero]
    refine ⟨?_, fun h => absurd h (by omega)⟩
    have := ModP.iso_sub (h0 4) (ModP.iso_of_eq ((hC (u12 p)).mul hX0) (by norm_num))
    simpa using this
  · simp only [show (2 : ℕ) ≠ 3 by decide, show (2 : ℕ) ≠ 1 by decide, show (2 : ℕ) ≠ 0 by decide,
      if_false, sub_zero, add_zero]
    exact ⟨h0 _, fun _ => trivial⟩
  · simp only [if_true, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 0 by decide, if_false, sub_zero,
      add_zero]
    refine ⟨?_, fun h => absurd h (by omega)⟩
    have := hC 4
    simpa [map_ofNat] using this
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), sub_zero, add_zero]
    exact ⟨h0 _, fun _ => rfl⟩

/-- **`hassePoly` is isobaric of weight `p − 1`.** -/
theorem iso_hassePoly (hp2 : p ≠ 2) : ModP.Iso (hassePoly p) (p - 1) := by
  have hodd := odd_p p hp2
  have := (good_pow p (good_gpoly p) ((p - 1) / 2) (p - 1)).1
  exact ModP.iso_of_eq this (by omega)

section Eval
variable {p} [CharP R p]

/-- the evaluation `X₀ ↦ c₄`, `X₁ ↦ −c₆`, `𝔽_p → R`. -/
noncomputable def evW (W : WeierstrassCurve R) : MvPolynomial (Fin 2) (ZMod p) →+* R :=
  MvPolynomial.eval₂Hom (ZMod.castHom (dvd_refl p) R) ![W.c₄, -W.c₆]

lemma twelve_ne_zero (hp5 : 5 ≤ p) : (12 : ZMod p) ≠ 0 := by
  intro h
  apply ModP.ne_zero_1728 hp5
  rw [show (1728 : ZMod p) = 12 ^ 3 by norm_num, h]; ring

/-- completing the cube: `g^{(c₄,−c₆)}(x) = f(x − b₂/12)`. -/
lemma map_gpoly (hp5 : 5 ≤ p) (W : WeierstrassCurve R) :
    (gpoly p).map (evW W) =
      (fpoly W).comp (X + C (-(W.b₂ * ZMod.castHom (dvd_refl p) R (u12 p)))) := by
  set u := ZMod.castHom (dvd_refl p) R (u12 p) with hu
  have h12 : (12 : R) * u = 1 := by
    rw [hu, u12, (map_ofNat (ZMod.castHom (dvd_refl p) R) 12).symm, ← map_mul,
      mul_inv_cancel₀ (twelve_ne_zero hp5), map_one]
  have hC12 : (12 : R[X]) * C u = 1 := by
    rw [(map_ofNat C 12).symm, ← map_mul, h12, map_one]
  simp only [gpoly, fpoly, evW, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, map_X, map_C, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    map_ofNat, map_mul, map_pow, add_comp, sub_comp, mul_comp, pow_comp, C_comp, X_comp,
    WeierstrassCurve.c₄, WeierstrassCurve.c₆, map_sub, map_add, map_neg, Polynomial.map_ofNat,
    ofNat_comp]
  rw [← hu]
  linear_combination (-(-X ^ 2 * C W.b₂ + X * C W.b₂ ^ 2 * C u - 2 * X * C W.b₄ -
    C W.b₂ ^ 3 * C u ^ 2 + 24 * C W.b₂ * C W.b₄ * C u ^ 2 + 2 * C W.b₂ * C W.b₄ * C u -
    144 * C W.b₆ * C u ^ 2 - 12 * C W.b₆ * C u - C W.b₆)) * hC12

/-- **`hassePoly(c₄, −c₆) = H(W)`** for every Weierstrass curve over a ring of characteristic `p ≥ 5`. -/
theorem eval_hassePoly (hp5 : 5 ≤ p) (W : WeierstrassCurve R) :
    evW W (hassePoly p) = hasseH p W := by
  have hodd := odd_p p (by omega)
  rw [hassePoly, ← Polynomial.coeff_map, Polynomial.map_pow, map_gpoly hp5, ← pow_comp,
    coeff_comp_shift p, ← hasseH_eq_coeff_fpoly p (by omega)]
  calc (fpoly W ^ ((p - 1) / 2)).natDegree ≤ (p - 1) / 2 * 3 :=
        natDegree_pow_le_of_le _ (natDegree_fpoly W)
    _ ≤ 2 * p - 2 := by omega

/-- **The Hasse invariant of the formal group as an isobaric polynomial in `(c₄, −c₆)`**:
in characteristic `p ≥ 5`, `a = hassePoly(c₄, −c₆)`. -/
theorem aH_formalGroup_eq_hassePoly (hp5 : 5 ≤ p) (W : WeierstrassCurve R) :
    FGL.aH p (EllipticFormal.formalGroup W) = evW W (hassePoly p) := by
  rw [eval_hassePoly hp5, aH_formalGroup_eq_hasseH p (by omega)]

end Eval

end Hasse

end HasseInv
