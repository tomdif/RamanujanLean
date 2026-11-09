/-
# Ramanujan's septic theta identity — Lost Notebook Entry 1.1(i)

Ramanujan (Lost Notebook, p. 206; Andrews–Berndt, *Lost Notebook* Part I/II; Son, Acta Arith. 98 (2001);
Rebák, Ramanujan J. 60 (2023), arXiv 2112.11884, eq. (11)):

  `φ(q^{1/7}) / φ(q⁷) = 1 + u + v + w`,
  `u = 2q^{1/7} f(q⁵,q⁹)/φ(q⁷)`, `v = 2q^{4/7} f(q³,q¹¹)/φ(q⁷)`, `w = 2q^{9/7} f(q,q¹³)/φ(q⁷)`,

with Ramanujan's general theta function `f(a,b) = Σ_{n∈ℤ} a^{n(n+1)/2} b^{n(n−1)/2}` and `φ(q) = f(q,q)`.
Replacing `q` by `q⁷` makes everything an integer power series:

  `φ(q)/φ(q⁴⁹) = 1 + u + v + w`,
  `u = 2q f(q³⁵,q⁶³)/φ(q⁴⁹)`, `v = 2q⁴ f(q²¹,q⁷⁷)/φ(q⁴⁹)`, `w = 2q⁹ f(q⁷,q⁹¹)/φ(q⁴⁹)`.

## Definitions

`ramF α β : ℤ⟦X⟧` is `f(q^α, q^β)`: the coefficient of `q^N` counts `n ∈ ℤ` with
`α n(n+1)/2 + β n(n−1)/2 = N` (stated without division as `α n(n+1) + β n(n−1) = 2N`). For `α, β ≥ 1` every
such `n` has `|n| ≤ N`, so the finite window `[-N, N]` in the definition loses nothing; `coeff_ramF` proves the
coefficient equals `Nat.card {n : ℤ // …}` (the honest bilateral sum). `φ(q^m) = f(q^m, q^m) = ramF m m`.

## Proof

The exponents collapse to squares: `1 + 35·n(n+1)/2 + 63·n(n−1)/2 = (7n−1)²`, similarly `(7n−2)²`, `(7n−3)²`,
and `49n² = (7n)²`. So the identity is the 7-dissection of `Σ_{k∈ℤ} q^{k²}` by `k mod 7`: the residue
classes `±1, ±2, ±3` pair off under `k ↦ −k`, giving the factors `2`. No `sorry`, no axioms beyond the standard three.
-/
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

namespace RamanujanTau.Septic

open PowerSeries

/-- Twice the exponent of the `n`-th term of `f(q^α, q^β)`: `α n(n+1) + β n(n−1)`. -/
def ex2 (α β : ℕ) (n : ℤ) : ℤ := (α : ℤ) * n * (n + 1) + (β : ℤ) * n * (n - 1)

/-- **Ramanujan's general theta function** `f(q^α, q^β) = Σ_{n∈ℤ} q^{α n(n+1)/2 + β n(n−1)/2}` as an
integer power series (for `α, β ≥ 1`; see `coeff_ramF`). -/
noncomputable def ramF (α β : ℕ) : PowerSeries ℤ :=
  mk fun N => (((Finset.Icc (-(N : ℤ)) N).filter (fun n => ex2 α β n = 2 * N)).card : ℤ)

/-- **Ramanujan's `φ(q) = f(q,q) = Σ_{n∈ℤ} q^{n²}`.** -/
noncomputable def phi : PowerSeries ℤ := ramF 1 1

lemma ex2_bound {α β : ℕ} (hα : 1 ≤ α) (hβ : 1 ≤ β) (n : ℤ) :
    0 ≤ ex2 α β n ∧ 2 * |n| ≤ ex2 α β n := by
  have hα' : (1 : ℤ) ≤ α := by exact_mod_cast hα
  have hβ' : (1 : ℤ) ≤ β := by exact_mod_cast hβ
  unfold ex2
  rcases le_or_gt 0 n with h | h
  · have h1 : 0 ≤ n * (n + 1) := by nlinarith
    have h2 : 0 ≤ n * (n - 1) := by nlinarith [sq_nonneg n]
    have h3 : n * (n + 1) ≤ (α : ℤ) * n * (n + 1) := by nlinarith
    have h4 : 0 ≤ (β : ℤ) * n * (n - 1) := by
      have := mul_nonneg (by linarith : (0 : ℤ) ≤ β) h2; linarith [this, mul_assoc (β : ℤ) n (n - 1)]
    rw [abs_of_nonneg h]
    constructor <;> nlinarith
  · have h1 : 0 ≤ n * (n + 1) := by nlinarith
    have h2 : 0 ≤ n * (n - 1) := by nlinarith
    have h3 : n * (n - 1) ≤ (β : ℤ) * n * (n - 1) := by nlinarith
    have h4 : 0 ≤ (α : ℤ) * n * (n + 1) := by
      have := mul_nonneg (by linarith : (0 : ℤ) ≤ α) h1; linarith [this, mul_assoc (α : ℤ) n (n + 1)]
    rw [abs_of_neg h]
    constructor <;> nlinarith

/-- The coefficient of `q^N` in `f(q^α,q^β)` is the number of `n ∈ ℤ` (no window) with exponent `N`. -/
theorem coeff_ramF {α β : ℕ} (hα : 1 ≤ α) (hβ : 1 ≤ β) (N : ℕ) :
    coeff N (ramF α β) = (Nat.card {n : ℤ // ex2 α β n = 2 * N} : ℤ) := by
  rw [ramF, coeff_mk]
  congr 1
  refine (Nat.subtype_card _ ?_).symm
  intro n
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    obtain ⟨_, h2⟩ := ex2_bound hα hβ n
    refine ⟨⟨?_, ?_⟩, h⟩ <;> cases abs_cases n <;> omega

/-- Coefficients of `q^j · f(q^α,q^β)`. -/
theorem coeff_X_pow_mul_ramF {α β : ℕ} (hα : 1 ≤ α) (hβ : 1 ≤ β) (j N : ℕ) :
    coeff N (X ^ j * ramF α β) = (Nat.card {n : ℤ // ex2 α β n + 2 * j = 2 * N} : ℤ) := by
  rw [coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_ramF hα hβ]
    have e : Nat.card {n : ℤ // ex2 α β n = 2 * ((N - j : ℕ) : ℤ)}
        = Nat.card {n : ℤ // ex2 α β n + 2 * (j : ℤ) = 2 * (N : ℤ)} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun n => by push_cast [Nat.cast_sub h]; omega)
    rw [e]
  · have : IsEmpty {n : ℤ // ex2 α β n + 2 * j = 2 * N} := ⟨fun ⟨n, hn⟩ => by
      have := (ex2_bound hα hβ n).1; omega⟩
    simp

/-! ### The 7-dissection of `{k : ℤ // k² = N}` -/

/-- Split `ℤ` by residue mod 7, restricted to a predicate. -/
def splitSeven (P : ℤ → Prop) : {k : ℤ // P k} ≃ Σ r : Fin 7, {n : ℤ // P (7 * n + (r : ℕ))} where
  toFun k := ⟨⟨(k.1 % 7).toNat, by omega⟩, ⟨k.1 / 7, by
    have h : 7 * (k.1 / 7) + (((k.1 % 7).toNat : ℕ) : ℤ) = k.1 := by omega
    simpa only [h] using k.2⟩⟩
  invFun s := ⟨7 * s.2.1 + (s.1 : ℕ), s.2.2⟩
  left_inv k := Subtype.ext (by simp only; omega)
  right_inv s := by
    rcases s with ⟨⟨r, hr⟩, n, hn⟩
    refine Sigma.subtype_ext (Fin.ext ?_) ?_ <;> simp <;> omega

lemma finite_sq (N : ℤ) : Finite {k : ℤ // k ^ 2 = N} := by
  refine Finite.of_injective
    (fun k : {k : ℤ // k ^ 2 = N} => (⟨k.1, ?_⟩ : Finset.Icc (-|N|) |N|)) ?_
  · obtain ⟨k, hk⟩ := k
    have : |k| ≤ k ^ 2 := by
      rcases abs_cases k with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> nlinarith
    simp only [Finset.mem_Icc]
    have hN : |N| = N := abs_of_nonneg (hk ▸ sq_nonneg k)
    constructor <;> cases abs_cases k <;> omega
  · intro a b h; exact Subtype.ext (by simpa using congrArg Subtype.val h)

lemma finite_class (N j : ℤ) : Finite {n : ℤ // (7 * n + j) ^ 2 = N} := by
  haveI := finite_sq N
  exact Finite.of_injective (fun n => (⟨7 * n.1 + j, n.2⟩ : {k : ℤ // k ^ 2 = N}))
    (fun a b h => Subtype.ext (by have := congrArg Subtype.val h; simp at this; omega))

/-- `c(j) := #{n ∈ ℤ : (7n + j)² = N}`. -/
noncomputable def cls (N j : ℤ) : ℕ := Nat.card {n : ℤ // (7 * n + j) ^ 2 = N}

lemma cls_neg (N j : ℤ) : cls N j = cls N (-j) := by
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.neg ℤ) fun n => ?_)
  have : (7 * (-n) + -j) ^ 2 = (7 * n + j) ^ 2 := by ring
  simp only [Equiv.neg_apply, this]

lemma cls_shift (N j : ℤ) : cls N (j + 7) = cls N j := by
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.addRight 1) fun n => ?_)
  have : 7 * (n + 1) + j = 7 * n + (j + 7) := by ring
  simp only [Equiv.coe_addRight, this]

/-- **The 7-dissection count.** `#{k : k² = N} = c(0) + 2c(−1) + 2c(−2) + 2c(−3)`. -/
theorem card_sq_seven (N : ℤ) :
    Nat.card {k : ℤ // k ^ 2 = N} = cls N 0 + 2 * cls N (-1) + 2 * cls N (-2) + 2 * cls N (-3) := by
  haveI : ∀ r : Fin 7, Finite {n : ℤ // (7 * n + ((r : ℕ) : ℤ)) ^ 2 = N} :=
    fun r => finite_class N _
  rw [Nat.card_congr (splitSeven _), Nat.card_sigma, Fin.sum_univ_seven]
  have e : ∀ r : ℕ, Nat.card {n : ℤ // (7 * n + ((r : ℕ) : ℤ)) ^ 2 = N} = cls N r := fun _ => rfl
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, e]
  have h3 : ((3 : Fin 7) : ℕ) = 3 := rfl
  have h4 : ((4 : Fin 7) : ℕ) = 4 := rfl
  have h5 : ((5 : Fin 7) : ℕ) = 5 := rfl
  have h6 : ((6 : Fin 7) : ℕ) = 6 := rfl
  rw [h3, h4, h5, h6]
  have c1 : cls N ((1 : ℕ) : ℤ) = cls N (-1) := by rw [cls_neg]; rfl
  have c2 : cls N ((2 : ℕ) : ℤ) = cls N (-2) := by rw [cls_neg]; rfl
  have c3 : cls N ((3 : ℕ) : ℤ) = cls N (-3) := by rw [cls_neg]; rfl
  have c4 : cls N ((4 : ℕ) : ℤ) = cls N (-3) := by
    rw [show ((4 : ℕ) : ℤ) = -3 + 7 by norm_num, cls_shift]
  have c5 : cls N ((5 : ℕ) : ℤ) = cls N (-2) := by
    rw [show ((5 : ℕ) : ℤ) = -2 + 7 by norm_num, cls_shift]
  have c6 : cls N ((6 : ℕ) : ℤ) = cls N (-1) := by
    rw [show ((6 : ℕ) : ℤ) = -1 + 7 by norm_num, cls_shift]
  rw [c1, c2, c3, c4, c5, c6]
  simp only [Nat.cast_zero]
  ring

/-! ### The series identity -/

private lemma card_eq_cls {α β j : ℕ} (hα : 1 ≤ α) (hβ : 1 ≤ β) (N : ℕ) (r : ℤ)
    (h : ∀ n : ℤ, ex2 α β n + 2 * (j : ℤ) = 2 * (7 * n + r) ^ 2) :
    coeff N (X ^ j * ramF α β) = (cls N r : ℤ) := by
  rw [coeff_X_pow_mul_ramF hα hβ]
  have e : Nat.card {n : ℤ // ex2 α β n + 2 * (j : ℤ) = 2 * (N : ℤ)}
      = Nat.card {n : ℤ // (7 * n + r) ^ 2 = (N : ℤ)} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun n => by rw [h n]; omega)
  rw [e]; rfl

/-- **The 7-dissection of `φ`** (Rebák's identity behind eq. (11), with `q ↦ q⁷`):
`φ(q) = φ(q⁴⁹) + 2q f(q³⁵,q⁶³) + 2q⁴ f(q²¹,q⁷⁷) + 2q⁹ f(q⁷,q⁹¹)`. -/
theorem phi_seven_dissection :
    phi = ramF 49 49 + 2 * X * ramF 35 63 + 2 * X ^ 4 * ramF 21 77 + 2 * X ^ 9 * ramF 7 91 := by
  ext N
  have hC : ∀ (j : ℕ) (F : PowerSeries ℤ), (2 : PowerSeries ℤ) * X ^ j * F = C (2 : ℤ) * (X ^ j * F) := by
    intro j F; rw [map_ofNat, mul_assoc]
  have hC1 : ∀ F : PowerSeries ℤ, (2 : PowerSeries ℤ) * X * F = C (2 : ℤ) * (X ^ 1 * F) := by
    intro F; rw [pow_one, map_ofNat, mul_assoc]
  rw [hC1, hC 4, hC 9]
  simp only [map_add, coeff_C_mul]
  have e0 : coeff N (ramF 49 49) = (cls N 0 : ℤ) := by
    rw [← one_mul (ramF 49 49), ← pow_zero X]
    exact card_eq_cls (by norm_num) (by norm_num) N 0 (fun n => by simp [ex2]; ring)
  rw [e0,
    card_eq_cls (j := 1) (by norm_num) (by norm_num) N (-1) (fun n => by simp [ex2]; ring),
    card_eq_cls (j := 4) (by norm_num) (by norm_num) N (-2) (fun n => by simp [ex2]; ring),
    card_eq_cls (j := 9) (by norm_num) (by norm_num) N (-3) (fun n => by simp [ex2]; ring)]
  rw [phi, coeff_ramF (by norm_num) (by norm_num)]
  have hk : Nat.card {k : ℤ // ex2 1 1 k = 2 * (N : ℤ)} = Nat.card {k : ℤ // k ^ 2 = (N : ℤ)} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun k => by
      have : ex2 1 1 k = 2 * k ^ 2 := by simp [ex2]; ring
      rw [this]; omega)
  rw [hk, card_sq_seven]
  push_cast
  ring

/-! ### Entry 1.1(i) in quotient form -/

lemma coeff_zero_ramF (α β : ℕ) : coeff 0 (ramF α β) = 1 := by
  rw [ramF, coeff_mk]
  have : (Finset.Icc (-((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ)).filter (fun n => ex2 α β n = 2 * ((0 : ℕ) : ℤ))
      = {0} := by
    ext n; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, _⟩; push_cast at h1 h2; omega
    · rintro rfl; simp [ex2]
  rw [this]; rfl

/-- `φ(q⁴⁹)` is a unit in `ℤ⟦q⟧` (constant term `1`). -/
lemma isUnit_phi49 : IsUnit (ramF 49 49) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply,
    coeff_zero_ramF 49 49]
  exact isUnit_one

/-- Rebák (11), `q ↦ q⁷`: `u = 2q f(q³⁵,q⁶³)/φ(q⁴⁹)`. -/
noncomputable def u : PowerSeries ℤ := 2 * X * ramF 35 63 * Ring.inverse (ramF 49 49)
/-- Rebák (11), `q ↦ q⁷`: `v = 2q⁴ f(q²¹,q⁷⁷)/φ(q⁴⁹)`. -/
noncomputable def v : PowerSeries ℤ := 2 * X ^ 4 * ramF 21 77 * Ring.inverse (ramF 49 49)
/-- Rebák (11), `q ↦ q⁷`: `w = 2q⁹ f(q⁷,q⁹¹)/φ(q⁴⁹)`. -/
noncomputable def w : PowerSeries ℤ := 2 * X ^ 9 * ramF 7 91 * Ring.inverse (ramF 49 49)

/-- **Ramanujan's septic theta identity, Lost Notebook Entry 1.1(i)** (in the variable `q⁷`):
`φ(q)/φ(q⁴⁹) = 1 + u + v + w`. -/
theorem septic_entry_1_1_i : phi * Ring.inverse (ramF 49 49) = 1 + u + v + w := by
  rw [phi_seven_dissection, u, v, w]
  have h := Ring.mul_inverse_cancel _ isUnit_phi49
  linear_combination h

end RamanujanTau.Septic
