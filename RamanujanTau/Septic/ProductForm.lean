/-
# Product forms for the septic `u, v, w` (Jacobi triple product)

Ramanujan's `f(a,b) = (−a;ab)_∞ (−b;ab)_∞ (ab;ab)_∞`. We obtain it for `a = q^α, b = q^β` with `α, β` odd
from the repo's signed triple product `RankProof.jtp_ab`
(`(q^b;q^a)_∞ (q^{a−b};q^a)_∞ (q^a;q^a)_∞ = Σ_{m∈ℤ} (−1)^m q^{a·m(m−1)/2+bm}`) by `q ↦ −q`
(`PowerSeries.rescale (−1)`): for `α, β` odd and `a = α+β` even, `(−1)^{exponent} = (−1)^m`, so the signs cancel,
and `rescale (−1) (Pinf b a) = ∏_{i≥0} (1 + q^{b+ai}) = (−q^b;q^a)_∞` (`b` odd, `a` even) while
`rescale (−1) (Pinf a a) = (q^a;q^a)_∞`.

All five thetas in Entry 1.1(i) have odd parameters: `φ(q) = f(q,q)`, `φ(q⁴⁹) = f(q⁴⁹,q⁴⁹)`,
`f(q³⁵,q⁶³)`, `f(q²¹,q⁷⁷)`, `f(q⁷,q⁹¹)`. No `sorry`.
-/
import RamanujanTau.Septic.Dissection
import RamanujanTau.RankTheta

namespace RamanujanTau.Septic

open PowerSeries Finset

lemma choose_two_mul (d : ℕ) : ((d.choose 2 : ℕ) : ℤ) * 2 = (d : ℤ) * ((d : ℤ) - 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.choose_succ_succ', Nat.choose_one_right]
    push_cast
    linear_combination ih

/-- exponent of the `m = d ≥ 0` term of `thetaS (α+β) α`, doubled, is `ex2 α β d`. -/
lemma expA (α β d : ℕ) :
    (((α + β) * d.choose 2 + α * d : ℕ) : ℤ) * 2 = ex2 α β (d : ℤ) := by
  have h := choose_two_mul d
  unfold ex2; push_cast
  linear_combination ((α : ℤ) + β) * h

/-- exponent of the `m = −(d+1)` term of `thetaS (α+β) α`, doubled, is `ex2 α β (−(d+1))`. -/
lemma expB (α β d : ℕ) :
    (((α + β) * (d + 1).choose 2 + (α + β - α) * (d + 1) : ℕ) : ℤ) * 2 = ex2 α β (-((d : ℤ) + 1)) := by
  have h := choose_two_mul (d + 1)
  rw [Nat.add_sub_cancel_left]
  unfold ex2; push_cast at h ⊢
  linear_combination ((α : ℤ) + β) * h

private lemma coeff_CXpow (c : ℤ) (e N : ℕ) :
    coeff N (C c * (X : PowerSeries ℤ) ^ e) = if N = e then c else 0 := by
  rw [coeff_C_mul, coeff_X_pow]; split_ifs <;> simp

/-- Signed sum over a finset, with the sign killed by parity, is a filter-card. -/
private lemma signed_sum {s : Finset ℕ} {E : ℕ → ℕ} {σ : ℕ → ℕ} (N : ℕ)
    (hpar : ∀ d ∈ s, N = E d → Even (N + σ d)) :
    (-1 : ℤ) ^ N * ∑ d ∈ s, (if N = E d then (-1 : ℤ) ^ σ d else 0)
      = ((s.filter fun d => N = E d).card : ℤ) := by
  rw [Finset.mul_sum, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun d hd => ?_
  split_ifs with h
  · rw [← pow_add]; exact (hpar d hd h).neg_one_pow
  · simp

/-- **`f(q^α,q^β) = (q ↦ −q) ∘ J_{α+β,α}`** for odd `α, β` (coefficientwise bijection `m ∈ ℤ`). -/
theorem ramF_eq_rescale_thetaS {α β : ℕ} (hα : Odd α) (hβ : Odd β) :
    ramF α β = rescale (-1) (RankProof.thetaS (α + β) α) := by
  have hα1 : 1 ≤ α := hα.pos
  have hβ1 : 1 ≤ β := hβ.pos
  ext N
  rw [coeff_rescale, RankProof.thetaS, coeff_mk, RankProof.thetaTr, map_add, map_sum, map_sum]
  simp only [coeff_CXpow]
  have hpa := signed_sum (s := range (N + 1)) (E := fun x => (α + β) * x.choose 2 + α * x)
    (σ := fun x => x) N (by
      intro d _ h; simp only at h ⊢; rw [h]
      rw [Nat.even_add, Nat.even_add, Nat.even_mul, Nat.even_mul, Nat.even_add]
      simp only [Nat.not_even_iff_odd.mpr hα, Nat.not_even_iff_odd.mpr hβ]; tauto)
  have hpb := signed_sum (s := range (N + 1))
    (E := fun x => (α + β) * (x + 1).choose 2 + (α + β - α) * (x + 1))
    (σ := fun x => x + 1) N (by
      intro d _ h; simp only at h ⊢; rw [h, Nat.add_sub_cancel_left]
      rw [Nat.even_add, Nat.even_add, Nat.even_mul, Nat.even_mul, Nat.even_add]
      simp only [Nat.not_even_iff_odd.mpr hα, Nat.not_even_iff_odd.mpr hβ]; tauto)
  simp only at hpa hpb
  rw [mul_add, hpa, hpb]
  rw [coeff_ramF hα1 hβ1, ← Nat.card_eq_finsetCard, ← Nat.card_eq_finsetCard, ← Nat.cast_add,
    ← Nat.card_sum]
  congr 1
  refine Nat.card_congr
    { toFun := fun m => if h : 0 ≤ m.1 then Sum.inl ⟨m.1.toNat, ?_⟩ else Sum.inr ⟨(-m.1 - 1).toNat, ?_⟩
      invFun := fun s => match s with
        | Sum.inl d => ⟨(d.1 : ℤ), ?_⟩
        | Sum.inr d => ⟨-((d.1 : ℤ) + 1), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · -- m ≥ 0
    have hm : ex2 α β m.1 = 2 * N := m.2
    have hb := (ex2_bound hα1 hβ1 m.1).2
    have e := expA α β m.1.toNat
    rw [Int.toNat_of_nonneg h] at e
    rw [abs_of_nonneg h] at hb
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor <;> omega
  · have hm : ex2 α β m.1 = 2 * N := m.2
    have hb := (ex2_bound hα1 hβ1 m.1).2
    have e := expB α β (-m.1 - 1).toNat
    rw [Int.toNat_of_nonneg (by omega), show -(-m.1 - 1 + 1) = m.1 by ring] at e
    rw [abs_of_neg (by omega)] at hb
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor <;> omega
  · have hd := d.2
    simp only [Finset.mem_filter, Finset.mem_range] at hd
    have e := expA α β d.1
    show ex2 α β (d.1 : ℤ) = 2 * N
    omega
  · have hd := d.2
    simp only [Finset.mem_filter, Finset.mem_range] at hd
    have e := expB α β d.1
    show ex2 α β (-((d.1 : ℤ) + 1)) = 2 * N
    omega
  · rintro ⟨m, hm⟩
    by_cases h : 0 ≤ m
    · simp only [h, dite_true]; exact Subtype.ext (by simp; omega)
    · simp only [h, dite_false]; exact Subtype.ext (by simp; omega)
  · rintro (⟨d, hd⟩ | ⟨d, hd⟩)
    · have : (0 : ℤ) ≤ d := by positivity
      simp [this]
    · have : ¬ (0 : ℤ) ≤ -((d : ℤ) + 1) := by omega
      simp only [this, dite_false, Sum.inr.injEq, Subtype.mk.injEq]
      omega

/-- **Jacobi triple product, Ramanujan's form**, for odd `α, β`:
`f(q^α,q^β) = (q ↦ −q)[(q^α;q^{α+β})_∞ (q^β;q^{α+β})_∞ (q^{α+β};q^{α+β})_∞]
= (−q^α;q^{α+β})_∞ (−q^β;q^{α+β})_∞ (q^{α+β};q^{α+β})_∞`. -/
theorem ramF_product {α β : ℕ} (hα : Odd α) (hβ : Odd β) :
    ramF α β = rescale (-1)
      (RankProof.Pinf α (α + β) * RankProof.Pinf β (α + β) * RankProof.Pinf (α + β) (α + β)) := by
  rw [ramF_eq_rescale_thetaS hα hβ, ← RankProof.jtp_ab (α + β) α hα.pos (by have := hβ.pos; omega),
    Nat.add_sub_cancel_left]

/-- `(q ↦ −q)` of `(q^b;q^a)_∞` coefficientwise: `rescale (−1) (Pinf b a) = ∏ (1 + q^{b+ai})` when `b` odd, `a`
even (finite-stage statement; the `Pinf` limit is coefficientwise). -/
lemma rescale_Pfin {b a : ℕ} (hb : Odd b) (ha : Even a) (M : ℕ) :
    rescale (-1 : ℤ) (RankProof.Pfin b a M) = ∏ i ∈ range M, (1 + X ^ (b + a * i)) := by
  rw [RankProof.Pfin, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hodd : Odd (b + a * i) := hb.add_even (ha.mul_right i)
  rw [map_sub, map_one, map_pow, rescale_X, mul_pow, ← map_pow, hodd.neg_one_pow]
  simp [sub_eq_add_neg]

/-- **Product forms of Entry 1.1(i)**: with `F(α,β) := (−q^α;q^{α+β})_∞ (−q^β;q^{α+β})_∞ (q^{α+β};q^{α+β})_∞`
(realised as `rescale (−1)` of the repo's `Pinf` products), `φ(q) = F(1,1)`, `φ(q⁴⁹) = F(49,49)` and
`u = 2q F(35,63)/F(49,49)`, `v = 2q⁴ F(21,77)/F(49,49)`, `w = 2q⁹ F(7,91)/F(49,49)`. -/
theorem septic_product_forms :
    phi = rescale (-1) (RankProof.Pinf 1 2 * RankProof.Pinf 1 2 * RankProof.Pinf 2 2) ∧
    ramF 49 49 = rescale (-1) (RankProof.Pinf 49 98 * RankProof.Pinf 49 98 * RankProof.Pinf 98 98) ∧
    ramF 35 63 = rescale (-1) (RankProof.Pinf 35 98 * RankProof.Pinf 63 98 * RankProof.Pinf 98 98) ∧
    ramF 21 77 = rescale (-1) (RankProof.Pinf 21 98 * RankProof.Pinf 77 98 * RankProof.Pinf 98 98) ∧
    ramF 7 91 = rescale (-1) (RankProof.Pinf 7 98 * RankProof.Pinf 91 98 * RankProof.Pinf 98 98) :=
  ⟨ramF_product (α := 1) (β := 1) (by decide) (by decide),
   ramF_product (α := 49) (β := 49) (by decide) (by decide),
   ramF_product (α := 35) (β := 63) (by decide) (by decide),
   ramF_product (α := 21) (β := 77) (by decide) (by decide),
   ramF_product (α := 7) (β := 91) (by decide) (by decide)⟩

end RamanujanTau.Septic
