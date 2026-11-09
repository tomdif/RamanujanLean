/-
# From `ℤ⟦q⟧` identities to real numbers (Rebák's step "(b)")

For `0 ≤ x`, the power series `F ∈ ℤ⟦q⟧` with `Σ |coeff n F| xⁿ < ∞` form a subring `convSub x`, and
`F ↦ Σ coeff n F · xⁿ` is a ring homomorphism `evHom x : convSub x →+* ℝ` (Cauchy product). Every
theta series in the septic chain lies in `convSub x` for `0 ≤ x < 1` (`ramF_mem`, coefficients `≤ 2N+1`),
so every identity in `ℤ⟦q⟧` between polynomial expressions in them holds for the real values.

The real values are identified with bilateral sums over `ℤ` by `hasSum_fibre`
(`Σ_{n∈ℤ} x^{g n} = Σ_N #{g = N} x^N` for `|n| ≤ g n`): `evR x (ramF m m) = phiR (x^m)` (`evR_ramF_mm`) and
`evR x (T r) = Σ_{n∈ℤ} x^{(7n+r)²}` (`evR_T`).
-/
import RamanujanTau.Septic.Quaternion
import RamanujanTau.Septic.Page206
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false

namespace RamanujanTau.Septic

open PowerSeries Finset

/-- `Σ |coeff n F| xⁿ < ∞`. -/
def AbsConv (x : ℝ) (F : PowerSeries ℤ) : Prop := Summable fun n => |((coeff n F : ℤ) : ℝ)| * x ^ n

/-- Real evaluation `Σ coeff n F · xⁿ`. -/
noncomputable def evR (x : ℝ) (F : PowerSeries ℤ) : ℝ := ∑' n, ((coeff n F : ℤ) : ℝ) * x ^ n

section closure

variable {x : ℝ} (hx : 0 ≤ x)
include hx

lemma AbsConv.summable {F : PowerSeries ℤ} (h : AbsConv x F) :
    Summable fun n => ((coeff n F : ℤ) : ℝ) * x ^ n := by
  refine Summable.of_norm ?_
  refine h.congr fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hx n)]

lemma AbsConv.norm {F : PowerSeries ℤ} (h : AbsConv x F) :
    Summable fun n => ‖((coeff n F : ℤ) : ℝ) * x ^ n‖ := by
  refine h.congr fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hx n)]

lemma absConv_add {F G : PowerSeries ℤ} (hF : AbsConv x F) (hG : AbsConv x G) :
    AbsConv x (F + G) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg hx n))
    (fun n => ?_) (hF.add hG)
  simp only [map_add, Int.cast_add]
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (pow_nonneg hx n)

lemma absConv_neg {F : PowerSeries ℤ} (hF : AbsConv x F) : AbsConv x (-F) := by
  refine hF.congr fun n => ?_
  simp

lemma absConv_mul {F G : PowerSeries ℤ} (hF : AbsConv x F) (hG : AbsConv x G) :
    AbsConv x (F * G) := by
  have h := summable_norm_sum_mul_antidiagonal_of_summable_norm (hF.norm hx) (hG.norm hx)
  refine h.congr fun n => ?_
  rw [coeff_mul, Real.norm_eq_abs]
  have : ∑ kl ∈ antidiagonal n, ((coeff kl.1 F : ℤ) : ℝ) * x ^ kl.1 * (((coeff kl.2 G : ℤ) : ℝ) * x ^ kl.2)
      = (∑ kl ∈ antidiagonal n, ((coeff kl.1 F : ℤ) : ℝ) * ((coeff kl.2 G : ℤ) : ℝ)) * x ^ n := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    rw [mem_antidiagonal] at hkl
    rw [← hkl, pow_add]; ring
  rw [this, abs_mul, abs_of_nonneg (pow_nonneg hx n)]
  push_cast; rfl

lemma evR_add {F G : PowerSeries ℤ} (hF : AbsConv x F) (hG : AbsConv x G) :
    evR x (F + G) = evR x F + evR x G := by
  unfold evR
  rw [← (hF.summable hx).tsum_add (hG.summable hx)]
  congr 1; funext n; simp only [map_add, Int.cast_add]; ring

lemma evR_mul {F G : PowerSeries ℤ} (hF : AbsConv x F) (hG : AbsConv x G) :
    evR x (F * G) = evR x F * evR x G := by
  unfold evR
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (hF.norm hx) (hG.norm hx)]
  congr 1; funext n
  rw [coeff_mul]; push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [mem_antidiagonal] at hkl
  rw [← hkl, pow_add]; ring

lemma absConv_C (k : ℤ) : AbsConv x (C k) := by
  refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
  rw [Finset.mem_singleton] at hn
  rw [coeff_C, if_neg hn]; simp

lemma evR_C (k : ℤ) : evR x (C k) = k := by
  unfold evR
  rw [tsum_eq_single 0 fun n hn => by rw [coeff_C, if_neg hn]; simp]
  simp

lemma absConv_X : AbsConv x X := by
  refine summable_of_ne_finset_zero (s := {1}) fun n hn => ?_
  rw [Finset.mem_singleton] at hn
  simp [coeff_X, hn]

lemma evR_X : evR x X = x := by
  unfold evR
  rw [tsum_eq_single 1 fun n hn => by simp [coeff_X, hn]]
  simp

end closure

/-- The subring of power series absolutely convergent at `x ≥ 0`. -/
def convSub (x : ℝ) (hx : 0 ≤ x) : Subring (PowerSeries ℤ) where
  carrier := {F | AbsConv x F}
  mul_mem' := absConv_mul hx
  one_mem' := by simpa using absConv_C hx 1
  add_mem' := absConv_add hx
  zero_mem' := by simpa using absConv_C hx 0
  neg_mem' := absConv_neg hx

/-- Evaluation at `x` as a ring homomorphism on `convSub x`. -/
noncomputable def evHom (x : ℝ) (hx : 0 ≤ x) : convSub x hx →+* ℝ where
  toFun F := evR x F.1
  map_one' := by simpa using evR_C hx 1
  map_mul' F G := evR_mul hx F.2 G.2
  map_zero' := by simpa using evR_C hx 0
  map_add' F G := evR_add hx F.2 G.2

/-! ### Bilateral sums by fibres -/

section fibre

variable {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)

omit hx0 hx1 in
lemma summable_two_mul_add_one (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Summable fun N : ℕ => (2 * (N : ℝ) + 1) * x ^ N := by
  have h1 : ‖x‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx1
  have hA := (summable_pow_mul_geometric_of_norm_lt_one 1 h1).mul_left 2
  have hB := summable_geometric_of_lt_one hx0 hx1
  refine (hA.add hB).congr fun N => ?_
  simp only [pow_one]; ring

variable (g : ℤ → ℕ) (hg : ∀ n, n.natAbs ≤ g n)
include hg

lemma fibre_inj (N : ℕ) : ∀ n : {n : ℤ // g n = N}, (n : ℤ) ∈ Finset.Icc (-(N : ℤ)) N := by
  intro n
  have h := hg n.1; rw [n.2] at h
  rw [Finset.mem_Icc]; omega

lemma finite_fibre_int (N : ℕ) : Finite {n : ℤ // g n = N} :=
  Finite.of_injective (fun n => (⟨n.1, fibre_inj g hg N n⟩ : Finset.Icc (-(N : ℤ)) N))
    fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h)

lemma card_fibre_le (N : ℕ) : Nat.card {n : ℤ // g n = N} ≤ 2 * N + 1 := by
  have := Nat.card_le_card_of_injective
    (fun n => (⟨n.1, fibre_inj g hg N n⟩ : Finset.Icc (-(N : ℤ)) N))
    fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h)
  rw [Nat.card_eq_finsetCard, Int.card_Icc] at this
  omega

include hx0 hx1

lemma summable_fibre : Summable fun N : ℕ => (Nat.card {n : ℤ // g n = N} : ℝ) * x ^ N :=
  Summable.of_nonneg_of_le (fun N => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx0 N))
    (fun N => mul_le_mul_of_nonneg_right (by exact_mod_cast card_fibre_le g hg N) (pow_nonneg hx0 N))
    (summable_two_mul_add_one hx0 hx1)

lemma tsum_fibre_eq (N : ℕ) :
    ∑' c : {n : ℤ // g n = N}, x ^ g c = (Nat.card {n : ℤ // g n = N} : ℝ) * x ^ N := by
  haveI := finite_fibre_int g hg N
  haveI := Fintype.ofFinite {n : ℤ // g n = N}
  rw [tsum_fintype]
  have : ∀ c : {n : ℤ // g n = N}, x ^ g c = x ^ N := fun c => by rw [c.2]
  simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

/-- **Fibrewise regrouping** `Σ_{n∈ℤ} x^{g n} = Σ_N #{g = N} x^N`. -/
theorem hasSum_fibre :
    HasSum (fun n => x ^ g n) (∑' N : ℕ, (Nat.card {n : ℤ // g n = N} : ℝ) * x ^ N) := by
  set e := Equiv.sigmaFiberEquiv g
  have hfin := finite_fibre_int g hg
  have hs : Summable fun s : (Σ N : ℕ, {n : ℤ // g n = N}) => x ^ g (e s) := by
    rw [summable_sigma_of_nonneg (fun s => pow_nonneg hx0 _)]
    refine ⟨fun N => ?_, ?_⟩
    · haveI := hfin N; exact Summable.of_finite
    · refine (summable_fibre hx0 hx1 g hg).congr fun N => ?_
      rw [← tsum_fibre_eq hx0 hx1 g hg N]; rfl
  have hs' : Summable fun n => x ^ g n := (e.summable_iff).mp hs
  convert hs'.hasSum using 1
  rw [← e.tsum_eq, hs.tsum_sigma']
  · congr 1; funext N
    exact (tsum_fibre_eq hx0 hx1 g hg N).symm
  · intro N; haveI := hfin N; exact Summable.of_finite

end fibre

/-! ### Membership of the theta series -/

section mem

variable {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
include hx0 hx1

lemma coeff_ramF_le (α β N : ℕ) : coeff N (ramF α β) ≤ 2 * N + 1 := by
  rw [ramF, coeff_mk]
  have := Finset.card_filter_le (Finset.Icc (-(N : ℤ)) N) (fun n => ex2 α β n = 2 * N)
  rw [Int.card_Icc] at this
  have h0 : ((N : ℤ) + 1 - -(N : ℤ)).toNat = 2 * N + 1 := by omega
  rw [h0] at this
  exact_mod_cast this

lemma ramF_mem (α β : ℕ) : AbsConv x (ramF α β) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg hx0 n))
    (fun N => mul_le_mul_of_nonneg_right ?_ (pow_nonneg hx0 N)) (summable_two_mul_add_one hx0 hx1)
  have h0 : (0 : ℤ) ≤ coeff N (ramF α β) := by rw [ramF, coeff_mk]; positivity
  rw [abs_of_nonneg (by exact_mod_cast h0)]
  exact_mod_cast coeff_ramF_le hx0 hx1 α β N

lemma Xpow_mem (j : ℕ) : AbsConv x (X ^ j) := by
  induction j with
  | zero => simpa using absConv_C hx0 1
  | succ j ih => rw [pow_succ]; exact absConv_mul hx0 ih (absConv_X hx0)

end mem

/-! ### Identification with bilateral sums -/

section ident

variable {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
include hx0 hx1

/-- `φ(q^m)` at `q = x` is `phiR (x^m)`. -/
theorem evR_ramF_mm {m : ℕ} (hm : 1 ≤ m) : evR x (ramF m m) = phiR (x ^ m) := by
  have hg : ∀ n : ℤ, n.natAbs ≤ m * n.natAbs ^ 2 := fun n => by
    rcases Nat.eq_zero_or_pos n.natAbs with h | h
    · rw [h]; simp
    · calc n.natAbs ≤ n.natAbs ^ 2 := Nat.le_self_pow (by norm_num) _
        _ ≤ m * n.natAbs ^ 2 := Nat.le_mul_of_pos_left _ hm
  have H := hasSum_fibre hx0 hx1 (fun n : ℤ => m * n.natAbs ^ 2) hg
  unfold phiR evR
  have e1 : (fun n : ℤ => (x ^ m) ^ (n.natAbs ^ 2)) = fun n => x ^ (m * n.natAbs ^ 2) := by
    funext n; rw [pow_mul]
  rw [e1, H.tsum_eq]
  congr 1; funext N
  rw [coeff_ramF hm hm]
  congr 1
  have e : {n : ℤ // ex2 m m n = 2 * (N : ℤ)} ≃ {n : ℤ // m * n.natAbs ^ 2 = N} :=
    Equiv.subtypeEquivRight fun n => by
      have h1 : ex2 m m n = 2 * (m * n ^ 2) := by simp [ex2]; ring
      have h2 : ((n.natAbs ^ 2 : ℕ) : ℤ) = n ^ 2 := by rw [Nat.cast_pow]; exact Int.natAbs_sq n
      have h3 : ((m * n.natAbs ^ 2 : ℕ) : ℤ) = m * n ^ 2 := by rw [Nat.cast_mul, h2]
      constructor
      · intro h
        have : ((m * n.natAbs ^ 2 : ℕ) : ℤ) = N := by rw [h3]; linarith
        exact_mod_cast this
      · intro h
        have := congrArg (Nat.cast (R := ℤ)) h
        rw [h3] at this; rw [h1, this]
  rw [Nat.card_congr e]; push_cast; rfl

lemma T_mem_of (r : ℤ) {α β j : ℕ} (h : T r = X ^ j * ramF α β) : AbsConv x (T r) := by
  rw [h]; exact absConv_mul hx0 (Xpow_mem hx0 hx1 j) (ramF_mem hx0 hx1 α β)

lemma T0_mem : AbsConv x (T 0) := T_mem_of hx0 hx1 0 (j := 0) (by rw [T0_eq, pow_zero, one_mul])
lemma T1_mem : AbsConv x (T 1) := T_mem_of hx0 hx1 1 (j := 1) (by rw [T1_eq, pow_one])
lemma T2_mem : AbsConv x (T 2) := T_mem_of hx0 hx1 2 T2_eq
lemma T3_mem : AbsConv x (T 3) := T_mem_of hx0 hx1 3 T3_eq

/-- `T r` at `x` is the bilateral sum `Σ_{n∈ℤ} x^{(7n+r)²}` (`0 ≤ r ≤ 6`). -/
theorem evR_T {r : ℤ} (hr0 : 0 ≤ r) (hr6 : r ≤ 6) :
    evR x (T r) = ∑' n : ℤ, x ^ ((7 * n + r) ^ 2).toNat := by
  have hg : ∀ n : ℤ, n.natAbs ≤ ((7 * n + r) ^ 2).toNat := fun n => by
    have h1 : (n.natAbs : ℤ) ≤ |7 * n + r| := by
      rcases le_or_gt 0 n with h | h
      · rw [abs_of_nonneg (by omega)]; omega
      · rw [abs_of_neg (by omega)]; omega
    have h2 : |7 * n + r| ≤ (7 * n + r) ^ 2 := by
      rcases abs_cases (7 * n + r) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> nlinarith
    have h3 : (((7 * n + r) ^ 2).toNat : ℤ) = (7 * n + r) ^ 2 := Int.toNat_of_nonneg (sq_nonneg _)
    omega
  rw [(hasSum_fibre hx0 hx1 _ hg).tsum_eq]
  unfold evR
  congr 1; funext N
  rw [T, coeff_cnt]
  congr 1
  have e : {n : ℤ // (7 * n + r) ^ 2 = (N : ℤ)} ≃ {n : ℤ // ((7 * n + r) ^ 2).toNat = N} :=
    Equiv.subtypeEquivRight fun n => by
      have h3 : (((7 * n + r) ^ 2).toNat : ℤ) = (7 * n + r) ^ 2 :=
        Int.toNat_of_nonneg (sq_nonneg _)
      omega
  rw [Nat.card_congr e]; push_cast; rfl

end ident

end RamanujanTau.Septic
