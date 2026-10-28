import RamanujanTau.TauModular
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Isobaric polynomials in `E₄, E₆` and their q-expansions over an arbitrary ring

We work with `MvPolynomial (Fin 2) R` (variables `X 0 ↦ E₄`, `X 1 ↦ E₆`) graded by the weights `(4, 6)`.
`Iso P k` means `P` is isobaric (weighted homogeneous) of weight `k`. The evaluation map
`ev R : R[X₀, X₁] → R⟦q⟧` sends `X 0 ↦ E₄ = 1 + 240 Σ σ₃(n)qⁿ`, `X 1 ↦ E₆ = 1 − 504 Σ σ₅(n)qⁿ`.

Main results (for any commutative ring `R` in which `1728` is a unit):
* `exists_div` — every isobaric `P` of weight `k` is `P(1,1)·base k + (X₀³ − X₁²)·Q` with `Q` isobaric of
  weight `k − 12` (and `Q = 0` when `k < 12`);
* `ev_disc` — `(X₀³ − X₁²)(E₄,E₆) = 1728·Δ` with `Δ = q∏(1 − qⁿ)²⁴`;
* `iso_eq_zero_of_ev_eq_zero` — **single-weight q-expansion principle**: an isobaric polynomial whose
  q-expansion vanishes is zero;
* `descend` — if `φ : R → S` is injective and `P ∈ S[X₀,X₁]` is isobaric with q-expansion in the image of
  `R⟦q⟧`, then `P` itself has coefficients in `R` (with an isobaric preimage).
-/

set_option autoImplicit false

namespace ModP
open MvPolynomial
open RamanujanTau.Mod691 (p4 p6 coeff_p4 coeff_p6)

/-- The weights `(4, 6)` of `E₄, E₆`. -/
def wt : Fin 2 → ℕ := ![4, 6]

/-- `P` is isobaric of weight `k` (weighted homogeneous for the weights `(4,6)`). -/
abbrev Iso {R : Type*} [CommSemiring R] (P : MvPolynomial (Fin 2) R) (k : ℕ) : Prop :=
  P.IsWeightedHomogeneous wt k

section Monomials
variable {R : Type*} [CommRing R]

lemma weight_wt (d : Fin 2 →₀ ℕ) : Finsupp.weight wt d = 4 * d 0 + 6 * d 1 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]
  simp [wt, mul_comm]

lemma iso_mono (a b : ℕ) : Iso (X 0 ^ a * X 1 ^ b : MvPolynomial (Fin 2) R) (4 * a + 6 * b) := by
  have h := ((isWeightedHomogeneous_X R wt 0).pow a).mul ((isWeightedHomogeneous_X R wt 1).pow b)
  convert h using 1
  simp [wt, mul_comm]

lemma iso_of_eq {P : MvPolynomial (Fin 2) R} {k k' : ℕ} (h : Iso P k) (hk : k = k') : Iso P k' := hk ▸ h

lemma iso_sub {P P' : MvPolynomial (Fin 2) R} {k : ℕ} (h : Iso P k) (h' : Iso P' k) : Iso (P - P') k := by
  exact Submodule.sub_mem (weightedHomogeneousSubmodule R wt k) h h'

lemma monomial_eq_two (d : Fin 2 →₀ ℕ) (r : R) :
    monomial d r = C r * (X 0 ^ d 0 * X 1 ^ d 1) := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]

/-- Exponents of the base monomial of weight `k`. -/
def bexp0 (k : ℕ) : ℕ := (k - 6 * ((k / 2) % 2)) / 4
/-- Exponents of the base monomial of weight `k`. -/
def bexp1 (k : ℕ) : ℕ := (k / 2) % 2

/-- The base monomial `X₀^a X₁^ε` of weight `k` (meaningful when `k` is a realizable weight). -/
noncomputable def base (k : ℕ) : MvPolynomial (Fin 2) R := X 0 ^ bexp0 k * X 1 ^ bexp1 k

lemma iso_base {k a b : ℕ} (hk : 4 * a + 6 * b = k) : Iso (base k : MvPolynomial (Fin 2) R) k := by
  subst hk
  have h0 : bexp0 (4 * a + 6 * b) = a + 3 * (b / 2) := by unfold bexp0; omega
  have h1 : bexp1 (4 * a + 6 * b) = b % 2 := by unfold bexp1; omega
  unfold base
  rw [h0, h1]
  exact iso_of_eq (iso_mono _ _) (by omega)

lemma map_base {S : Type*} [CommRing S] (φ : R →+* S) (k : ℕ) :
    MvPolynomial.map φ (base k : MvPolynomial (Fin 2) R) = base k := by
  simp [base]

/-- The one point `(1,1)`. -/
def one2 : Fin 2 → R := fun _ => 1

lemma eval_base (k : ℕ) : eval (one2 : Fin 2 → R) (base k) = 1 := by
  simp [base, one2]

/-- Division of a monomial by `X₀³ − X₁²` modulo the base monomial. -/
lemma mono_decomp (a b : ℕ) : ∃ Q : MvPolynomial (Fin 2) R, Iso Q (4 * a + 6 * b - 12) ∧
    (4 * a + 6 * b < 12 → Q = 0) ∧
    X 0 ^ a * X 1 ^ b = base (4 * a + 6 * b) + (X 0 ^ 3 - X 1 ^ 2) * Q := by
  set e := b % 2 with he
  set j := b / 2 with hj
  have hb : b = e + 2 * j := by omega
  have h0 : bexp0 (4 * a + 6 * b) = a + 3 * j := by unfold bexp0; omega
  have h1 : bexp1 (4 * a + 6 * b) = e := by unfold bexp1; omega
  set S : MvPolynomial (Fin 2) R :=
    ∑ i ∈ Finset.range j, X 0 ^ (a + 3 * i) * X 1 ^ (e + 2 * (j - 1 - i)) with hS
  refine ⟨C (-1) * S, ?_, ?_, ?_⟩
  · apply IsWeightedHomogeneous.C_mul
    apply IsWeightedHomogeneous.sum
    intro i hi
    rw [Finset.mem_range] at hi
    exact iso_of_eq (iso_mono _ _) (by omega)
  · intro hlt
    have : j = 0 := by omega
    simp [hS, this]
  · have hS' : S = X 0 ^ a * X 1 ^ e *
        ∑ i ∈ Finset.range j, (X 0 ^ 3) ^ i * (X 1 ^ 2) ^ (j - 1 - i) := by
      rw [hS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_add, pow_add, pow_mul, pow_mul]; ring
    have hG := geom_sum₂_mul (X 0 ^ 3 : MvPolynomial (Fin 2) R) (X 1 ^ 2) j
    rw [base, h0, h1, hS', hb]
    rw [← pow_mul, ← pow_mul] at hG
    have e1 : (X 0 : MvPolynomial (Fin 2) R) ^ (a + 3 * j) = X 0 ^ a * X 0 ^ (3 * j) := pow_add _ _ _
    have e2 : (X 1 : MvPolynomial (Fin 2) R) ^ (e + 2 * j) = X 1 ^ e * X 1 ^ (2 * j) := pow_add _ _ _
    rw [e1, e2, map_neg, map_one]
    linear_combination (X 0 ^ a * X 1 ^ e) * hG

/-- **Division lemma.** An isobaric `P` of weight `k` is `P(1,1)·base k + (X₀³ − X₁²)·Q`, `Q` isobaric of
weight `k − 12`, `Q = 0` if `k < 12`. -/
theorem exists_div {k : ℕ} {P : MvPolynomial (Fin 2) R} (hP : Iso P k) :
    ∃ Q : MvPolynomial (Fin 2) R, Iso Q (k - 12) ∧ (k < 12 → Q = 0) ∧
      P = C (eval one2 P) * base k + (X 0 ^ 3 - X 1 ^ 2) * Q := by
  induction hP using IsWeightedHomogeneous.induction_on with
  | zero => exact ⟨0, isWeightedHomogeneous_zero R wt _, fun _ => rfl, by simp⟩
  | add p q hp hq ihp ihq =>
    obtain ⟨Q₁, h₁, h₁', e₁⟩ := ihp
    obtain ⟨Q₂, h₂, h₂', e₂⟩ := ihq
    refine ⟨Q₁ + Q₂, h₁.add h₂, fun h => by rw [h₁' h, h₂' h, add_zero], ?_⟩
    rw [map_add, map_add]
    conv_lhs => rw [e₁, e₂]
    ring
  | monomial d r hr =>
    rw [weight_wt] at hr
    obtain ⟨Q, hQ, hQ0, hQe⟩ := mono_decomp (R := R) (d 0) (d 1)
    rw [hr] at hQ hQ0 hQe
    refine ⟨C r * Q, hQ.C_mul r, fun h => by rw [hQ0 h, mul_zero], ?_⟩
    rw [monomial_eq_two, hQe]
    have he : eval one2 (C r * (base k + (X 0 ^ 3 - X 1 ^ 2) * Q)) = r := by
      rw [map_mul, eval_C, map_add, eval_base, map_mul, map_sub, map_pow, map_pow, eval_X, eval_X]
      simp [one2]
    rw [he]
    ring

end Monomials

section Eval

lemma psmap_map {A B C' : Type*} [CommRing A] [CommRing B] [CommRing C'] (f : A →+* B) (g : B →+* C')
    (x : PowerSeries A) : PowerSeries.map g (PowerSeries.map f x) = PowerSeries.map (g.comp f) x := by
  rw [PowerSeries.map_comp]; rfl

variable (R : Type*) [CommRing R]

/-- `E₄ ∈ R⟦q⟧`. -/
noncomputable def E4 : PowerSeries R := PowerSeries.map (Int.castRingHom R) p4
/-- `E₆ ∈ R⟦q⟧`. -/
noncomputable def E6 : PowerSeries R := PowerSeries.map (Int.castRingHom R) p6
/-- `Δ = q ∏ (1 − qⁿ)²⁴ ∈ R⟦q⟧`. -/
noncomputable def Dq : PowerSeries R :=
  PowerSeries.map (Int.castRingHom R) (PowerSeries.X * MockTheta5.JTP.qfacInf ^ 24)

/-- The evaluation vector `(E₄, E₆)`. -/
noncomputable def evVec : Fin 2 → PowerSeries R := ![E4 R, E6 R]

/-- **The q-expansion map** `R[X₀,X₁] → R⟦q⟧`, `X₀ ↦ E₄`, `X₁ ↦ E₆`. -/
noncomputable def ev : MvPolynomial (Fin 2) R →ₐ[R] PowerSeries R := aeval (evVec R)

@[simp] lemma ev_X0 : ev R (X 0) = E4 R := by simp [ev, evVec]
@[simp] lemma ev_X1 : ev R (X 1) = E6 R := by simp [ev, evVec]

lemma constantCoeff_E4 : PowerSeries.constantCoeff (E4 R) = 1 := by
  rw [E4, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, coeff_p4]; simp

lemma constantCoeff_E6 : PowerSeries.constantCoeff (E6 R) = 1 := by
  rw [E6, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, coeff_p6]; simp

/-- `(X₀³ − X₁²)(E₄, E₆) = 1728 Δ`. -/
theorem ev_disc : ev R (X 0 ^ 3 - X 1 ^ 2) = 1728 * Dq R := by
  have h := congrArg (PowerSeries.map (Int.castRingHom R))
    RamanujanTau.TauModular.discriminant_formal_identity
  simp only [map_mul, map_sub, map_pow, map_ofNat] at h
  simp only [map_sub, map_pow, ev_X0, ev_X1, E4, E6, Dq, map_mul, map_pow]
  rw [h]

/-- The constant term of the q-expansion is the value at `(1,1)`. -/
theorem constantCoeff_ev (P : MvPolynomial (Fin 2) R) :
    PowerSeries.constantCoeff (ev R P) = eval one2 P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [ev]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp, map_mul, eval_X]
    fin_cases i
    · simp [constantCoeff_E4, one2]
    · simp [constantCoeff_E6, one2]

variable {R}

lemma map_E4 {S : Type*} [CommRing S] (φ : R →+* S) : PowerSeries.map φ (E4 R) = E4 S := by
  rw [E4, E4, psmap_map, show φ.comp (Int.castRingHom R) = Int.castRingHom S from RingHom.ext_int _ _]

lemma map_E6 {S : Type*} [CommRing S] (φ : R →+* S) : PowerSeries.map φ (E6 R) = E6 S := by
  rw [E6, E6, psmap_map, show φ.comp (Int.castRingHom R) = Int.castRingHom S from RingHom.ext_int _ _]

lemma map_Dq {S : Type*} [CommRing S] (φ : R →+* S) : PowerSeries.map φ (Dq R) = Dq S := by
  rw [Dq, Dq, psmap_map, show φ.comp (Int.castRingHom R) = Int.castRingHom S from RingHom.ext_int _ _]

/-- The q-expansion map commutes with change of coefficients. -/
theorem map_ev {S : Type*} [CommRing S] (φ : R →+* S) (P : MvPolynomial (Fin 2) R) :
    PowerSeries.map φ (ev R P) = ev S (MvPolynomial.map φ P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [ev]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp, map_mul, map_mul, map_X]
    fin_cases i
    · simp [map_E4]
    · simp [map_E6]

/-- `Δ = q·U` with `U` a unit (over `ℤ`). -/
lemma exists_inv_U : ∃ W : PowerSeries ℤ, MockTheta5.JTP.qfacInf ^ 24 * W = 1 :=
  (MockTheta5.JTP.isUnit_qfacInf.pow 24).exists_right_inv

/-- Cancellation of `1728 Δ` in `R⟦q⟧` when `1728` is a unit of `R`. -/
lemma eq_zero_of_disc_mul (h1728 : IsUnit (1728 : R)) {g : PowerSeries R}
    (hg : 1728 * Dq R * g = 0) : g = 0 := by
  obtain ⟨W, hW⟩ := exists_inv_U
  obtain ⟨u, hu⟩ := h1728.exists_left_inv
  have hW' : PowerSeries.map (Int.castRingHom R) W * PowerSeries.map (Int.castRingHom R)
      (MockTheta5.JTP.qfacInf ^ 24) = 1 := by
    rw [← map_mul, mul_comm, hW, map_one]
  have key : PowerSeries.X * g = 0 := by
    have := congrArg (fun t => PowerSeries.C u * PowerSeries.map (Int.castRingHom R) W * t) hg
    simp only [mul_zero] at this
    rw [← this, Dq, map_mul, PowerSeries.map_X]
    have h1 : (PowerSeries.C u : PowerSeries R) * 1728 = 1 := by
      rw [show (1728 : PowerSeries R) = PowerSeries.C 1728 from (map_ofNat _ _).symm, ← map_mul, hu, map_one]
    linear_combination (-(PowerSeries.X * g) * (PowerSeries.map (Int.castRingHom R) W *
      PowerSeries.map (Int.castRingHom R) (MockTheta5.JTP.qfacInf ^ 24))) * h1 +
      (-(PowerSeries.X * g)) * hW'
  exact PowerSeries.X_mul_cancel (by rw [key, mul_zero])

/-- Division by `1728 Δ` descends along an injective ring map. -/
lemma descend_disc {S : Type*} [CommRing S] (φ : R →+* S) (hφ : Function.Injective φ)
    (h1728 : IsUnit (1728 : R)) {g : PowerSeries S} {h : PowerSeries R}
    (hg : PowerSeries.map φ h = 1728 * Dq S * g) : ∃ g₀ : PowerSeries R, PowerSeries.map φ g₀ = g := by
  obtain ⟨W, hW⟩ := exists_inv_U
  obtain ⟨u, hu⟩ := h1728.exists_left_inv
  set h'' := PowerSeries.C u * PowerSeries.map (Int.castRingHom R) W * h with hh''
  have hmap : PowerSeries.map φ h'' = PowerSeries.X * g := by
    rw [hh'', map_mul, map_mul, hg, PowerSeries.map_C, psmap_map, Dq, map_mul,
      PowerSeries.map_X]
    have e1 : (φ.comp (Int.castRingHom R)) = Int.castRingHom S := RingHom.ext_int _ _
    have hW' : PowerSeries.map (Int.castRingHom S) W * PowerSeries.map (Int.castRingHom S)
        (MockTheta5.JTP.qfacInf ^ 24) = 1 := by
      rw [← map_mul, mul_comm, hW, map_one]
    have h1 : (PowerSeries.C (φ u) : PowerSeries S) * 1728 = 1 := by
      rw [show (1728 : PowerSeries S) = PowerSeries.C 1728 from (map_ofNat _ _).symm, ← map_mul,
        show (1728 : S) = φ 1728 from (map_ofNat _ _).symm, ← map_mul, hu, map_one, map_one]
    rw [e1]
    linear_combination (PowerSeries.X * g) * (PowerSeries.C (φ u) * 1728) * hW' +
      (PowerSeries.X * g) * h1
  have hcc : PowerSeries.constantCoeff h'' = 0 := by
    apply hφ
    rw [map_zero, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_map, hmap,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, PowerSeries.constantCoeff_X, zero_mul]
  obtain ⟨g₀, hg₀⟩ := PowerSeries.X_dvd_iff.mpr hcc
  refine ⟨g₀, PowerSeries.X_mul_cancel ?_⟩
  rw [← hmap, hg₀, map_mul, PowerSeries.map_X]

end Eval

section Main
variable {R : Type*} [CommRing R]

/-- **Single-weight q-expansion principle.** If `1728` is a unit in `R`, an isobaric polynomial
`P ∈ R[X₀,X₁]` with `P(E₄,E₆) = 0` in `R⟦q⟧` is zero. -/
theorem iso_eq_zero_of_ev_eq_zero (h1728 : IsUnit (1728 : R)) :
    ∀ (k : ℕ) (P : MvPolynomial (Fin 2) R), Iso P k → ev R P = 0 → P = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro P hP hev
    obtain ⟨Q, hQ, hQ0, hPQ⟩ := exists_div hP
    have hs : eval one2 P = 0 := by rw [← constantCoeff_ev, hev, map_zero]
    rw [hs, map_zero, zero_mul, zero_add] at hPQ
    have hQev : ev R Q = 0 := by
      apply eq_zero_of_disc_mul h1728
      rw [← ev_disc, ← map_mul, ← hPQ, hev]
    by_cases hk : k < 12
    · rw [hPQ, hQ0 hk, mul_zero]
    · rw [hPQ, ih (k - 12) (by omega) Q hQ hQev, mul_zero]

/-- Injectivity of the q-expansion map on each isobaric piece. -/
theorem ev_injOn_iso (h1728 : IsUnit (1728 : R)) {k : ℕ} {P P' : MvPolynomial (Fin 2) R}
    (hP : Iso P k) (hP' : Iso P' k) (h : ev R P = ev R P') : P = P' := by
  have := iso_eq_zero_of_ev_eq_zero h1728 k (P - P') (iso_sub hP hP') (by rw [map_sub, h, sub_self])
  exact sub_eq_zero.mp this

/-- **Descent of isobaric polynomials.** Let `φ : R → S` be injective with `1728` a unit of `R`. If
`P ∈ S[X₀,X₁]` is isobaric of weight `k` and `P(E₄,E₆) ∈ S⟦q⟧` comes from `R⟦q⟧`, then `P = φ(P₀)` for an
isobaric `P₀ ∈ R[X₀,X₁]` of weight `k`. -/
theorem descend {S : Type*} [CommRing S] (φ : R →+* S) (hφ : Function.Injective φ)
    (h1728 : IsUnit (1728 : R)) :
    ∀ (k : ℕ) (P : MvPolynomial (Fin 2) S), Iso P k →
      (∃ h : PowerSeries R, PowerSeries.map φ h = ev S P) →
      ∃ P₀ : MvPolynomial (Fin 2) R, Iso P₀ k ∧ MvPolynomial.map φ P₀ = P := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro P hP ⟨h, hh⟩
    by_cases hP0 : P = 0
    · exact ⟨0, isWeightedHomogeneous_zero R wt k, by rw [hP0, map_zero]⟩
    obtain ⟨d, hd⟩ : ∃ d, coeff d P ≠ 0 := by
      by_contra hc; push Not at hc; exact hP0 (MvPolynomial.ext _ _ fun d => by simp [hc d])
    have hk : 4 * d 0 + 6 * d 1 = k := by rw [← weight_wt]; exact hP hd
    obtain ⟨Q, hQ, hQ0, hPQ⟩ := exists_div hP
    set s := eval one2 P with hsdef
    set r := PowerSeries.constantCoeff h with hr
    have hs : s = φ r := by
      rw [hsdef, ← constantCoeff_ev, ← hh, hr, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    have hevP : ev S P = PowerSeries.C s * ev S (base k) + 1728 * Dq S * ev S Q := by
      conv_lhs => rw [hPQ]
      rw [map_add, map_mul, map_mul, ev_disc]
      simp [ev]
    -- the q-expansion of `Q` descends
    have hQd : ∃ g₀ : PowerSeries R, PowerSeries.map φ g₀ = ev S Q := by
      apply descend_disc φ hφ h1728 (h := h - PowerSeries.C r * ev R (base k))
      rw [map_sub, map_mul, PowerSeries.map_C, map_ev, map_base, hh, ← hs, hevP]
      ring
    have hbase : Iso (base k : MvPolynomial (Fin 2) R) k := iso_base hk
    by_cases hk12 : k < 12
    · refine ⟨C r * base k, hbase.C_mul r, ?_⟩
      rw [map_mul, map_C, map_base, ← hs]
      conv_rhs => rw [hPQ, hQ0 hk12]
      simp
    · obtain ⟨Q₀, hQ₀, hQ₀e⟩ := ih (k - 12) (by omega) Q hQ hQd
      refine ⟨C r * base k + (X 0 ^ 3 - X 1 ^ 2) * Q₀, (hbase.C_mul r).add ?_, ?_⟩
      · have h12 : Iso (X 0 ^ 3 - X 1 ^ 2 : MvPolynomial (Fin 2) R) 12 :=
          iso_sub (iso_of_eq (by simpa using iso_mono (R := R) 3 0) (by norm_num))
            (iso_of_eq (by simpa using iso_mono (R := R) 0 2) (by norm_num))
        exact iso_of_eq (h12.mul hQ₀) (by omega)
      · rw [map_add, map_mul, map_C, map_base, map_mul, hQ₀e, ← hs]
        conv_rhs => rw [hPQ]
        simp

end Main

end ModP
