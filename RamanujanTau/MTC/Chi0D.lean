/-
# The Bailey double sum for `(q;q)_∞ χ₀` as eight `f_{12,9,3}` cones

`ιN₆ ((q;q)_∞ χ₀) = Cp 0 8 4 + Cp 1 11 5 − Cp 1 14 4 − Cp 2 17 5 + Cp 9 22 10 + Cp 12 25 11 − Cp 4 16 10 − Cp 7 19 11`.

The double sum `Σ_j c_j Σ_u (−1)^u q^{eC(r(j),u)}(1 + q^{r(j)+1+u})` (`Chi0.qfacInf_mul_chi0`) is first written as one
monomial family `H` over `(j, u, δ, ε) ∈ ℤ × ℕ × Bool × Bool`, then reindexed by `j = r` or `j = −1 − r`.
-/
import RamanujanTau.MTC.Chi0Theta
import RamanujanTau.Chi0Bailey

set_option autoImplicit false

namespace MTC.Chi0L
open ALz HahnSeries Finset MTC

/-! ## `ιN` of a stabilized sum -/

section PsFam
variable {N : ℕ} (hN : 1 ≤ N) {ι : Type*}

/-- the family `i ↦ ιN (T i)` when `T i` has order `≥ o i` and `o` has finite sublevel sets. -/
noncomputable def psFam (T : ι → PowerSeries ℤ) (o : ι → ℕ)
    (hT : ∀ i, (PowerSeries.X : PowerSeries ℤ) ^ o i ∣ T i) (hfin : ∀ m, {i | o i ≤ m}.Finite) :
    SummableFamily ℤ ℂ ι :=
  ofSupp (fun i => ιN hN (T i)) 0 (fun i n hn => ιN_coeff_neg hN _ hn) (fun n => (hfin n.toNat).subset fun i hi => by
    simp only [Set.mem_setOf_eq] at hi ⊢
    rcases lt_or_ge n 0 with h | h
    · exact absurd (ιN_coeff_neg hN _ h) hi
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k := ⟨n.toNat, by omega⟩
      rw [ιN_coeff_nat] at hi
      split_ifs at hi with hd
      · by_contra hlt
        apply hi
        obtain ⟨c, hc⟩ := hT i
        rw [hc, PowerSeries.coeff_X_pow_mul', if_neg (by have := Nat.div_le_self k N; omega)]
        simp
      · simp at hi)

lemma hs_psFam (T : ι → PowerSeries ℤ) (o : ι → ℕ) (hT : ∀ i, (PowerSeries.X : PowerSeries ℤ) ^ o i ∣ T i)
    (hfin : ∀ m, {i | o i ≤ m}.Finite) (P : PowerSeries ℤ) (S : ℕ → Finset ι)
    (hS : ∀ m i, o i ≤ m → i ∈ S m) (hP : ∀ m, PowerSeries.coeff m P = ∑ i ∈ S m, PowerSeries.coeff m (T i)) :
    hs (psFam hN T o hT hfin) = ιN hN P := by
  ext n
  rw [hs, SummableFamily.coeff_hsum]
  rcases lt_or_ge n 0 with hn | hn
  · rw [ιN_coeff_neg hN _ hn]
    exact finsum_eq_zero_of_forall_eq_zero fun i => ιN_coeff_neg hN _ hn
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k := ⟨n.toNat, by omega⟩
    simp only [psFam, ofSupp_apply, ιN_coeff_nat]
    by_cases hd : N ∣ k
    · simp only [if_pos hd]
      rw [hP, Int.cast_sum, finsum_eq_sum_of_support_subset (s := S (k / N))]
      intro i hi
      rw [Function.mem_support] at hi
      simp only [Finset.mem_coe]
      refine hS _ i ?_
      by_contra hlt
      apply hi
      obtain ⟨c, hc⟩ := hT i
      rw [hc, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
      simp
    · simp only [if_neg hd, finsum_zero]

end PsFam

/-! ## The two stabilized sums of the Bailey side -/

lemma tC_dvd' (j : ℤ) (u : ℕ) : (PowerSeries.X : PowerSeries ℤ) ^ u ∣ Chi0.cj j * Chi0.tC (Chi0.rj j) u :=
  dvd_mul_of_dvd_right (Chi0.X_pow_dvd_tC _ _) _

/-- the row `u ↦ ιN (c_j t_{r(j),u})`. -/
noncomputable def uFam (j : ℤ) : SummableFamily ℤ ℂ ℕ :=
  psFam h6 (fun u => Chi0.cj j * Chi0.tC (Chi0.rj j) u) id (tC_dvd' j) (fun m => Set.finite_Iic m)

lemma hs_uFam (j : ℤ) : hs (uFam j) = ιN h6 (Chi0.cj j * Chi0.Cc (Chi0.rj j)) :=
  hs_psFam h6 _ _ _ _ _ (fun m => range (m + 1)) (fun m i h => by simp only [id] at h; simp; omega)
    (fun m => by
      rw [← map_sum, ← mul_sum]
      exact Chi0.coeff_mul_of_dvd (Chi0.X_pow_dvd_sub_of_coeff fun m' hm' => Chi0.coeff_Cc (by omega)))

lemma cjCc_dvd (j : ℤ) : (PowerSeries.X : PowerSeries ℤ) ^ j.natAbs ∣ Chi0.cj j * Chi0.Cc (Chi0.rj j) :=
  dvd_mul_of_dvd_left (Chi0.cj_dvd j) _

lemma natAbs_fin (m : ℕ) : {j : ℤ | j.natAbs ≤ m}.Finite :=
  (Set.finite_Icc (-(m : ℤ)) m).subset fun j hj => by
    simp only [Set.mem_setOf_eq] at hj; simp only [Set.mem_Icc]; omega

/-- the family `j ↦ ιN (c_j γ_{r(j)})`. -/
noncomputable def jFam : SummableFamily ℤ ℂ ℤ :=
  psFam h6 (fun j => Chi0.cj j * Chi0.Cc (Chi0.rj j)) Int.natAbs cjCc_dvd natAbs_fin

lemma hs_jFam : hs jFam = ιN h6 (MockTheta5.JTP.qfacInf * MockTheta5.Formal.chi0) :=
  hs_psFam h6 _ _ _ _ _ (fun m => Icc (-(m : ℤ)) m) (fun m i h => by simp only [mem_Icc]; omega)
    (fun m => by rw [Chi0.qfacInf_mul_chi0, Chi0.coeff_zsum cjCc_dvd le_rfl, map_sum])

/-! ## The monomial family over `(j, u, δ, ε)` -/

/-- the exponent of `c_j`: `j(6j−1)` (`δ = false`) or `(2j+1)(3j+1)` (`δ = true`). -/
def eD (j : ℤ) (δ : Bool) : ℤ := if δ then (2 * j + 1) * (3 * j + 1) else j * (6 * j - 1)

lemma eD_ge (j : ℤ) (δ : Bool) : |j| ≤ eD j δ := by
  unfold eD
  cases δ <;> simp only [Bool.false_eq_true, if_false, if_true]
  · rcases (by omega : j ≤ 0 ∨ 1 ≤ j) with h | h
    · rw [abs_of_nonpos h]; nlinarith
    · rw [abs_of_nonneg (by omega)]; nlinarith
  · rcases (by omega : j ≤ -1 ∨ 0 ≤ j) with h | h
    · rw [abs_of_nonpos (by omega)]; nlinarith
    · rw [abs_of_nonneg h]; nlinarith

lemma eC_ge (r u : ℕ) : u ≤ Chi0.eC r u := by
  unfold Chi0.eC
  have : 2 * u ≤ u * (3 * u + 5) := by nlinarith
  omega

/-- `Q`-exponent (times 6) of the `(δ, ε)` monomial of `c_j t_{r(j),u}`. -/
def HE (p : ℤ × ℕ × Bool × Bool) : ℤ :=
  6 * (eD p.1 p.2.2.1 + (Chi0.eC (Chi0.rj p.1) p.2.1 : ℤ) +
    if p.2.2.2 then (Chi0.rj p.1 : ℤ) + 1 + p.2.1 else 0)

noncomputable def HC (p : ℤ × ℕ × Bool × Bool) : ℂ := (if p.2.2.1 then -1 else 1) * (-1) ^ p.2.1

lemma HE_ge (p : ℤ × ℕ × Bool × Bool) : |p.1| + p.2.1 ≤ HE p := by
  unfold HE
  have h1 := eD_ge p.1 p.2.2.1
  have h2 : ((p.2.1 : ℕ) : ℤ) ≤ (Chi0.eC (Chi0.rj p.1) p.2.1 : ℤ) := by exact_mod_cast eC_ge _ _
  have h3 : (0 : ℤ) ≤ if p.2.2.2 then (Chi0.rj p.1 : ℤ) + 1 + p.2.1 else 0 := by split_ifs <;> positivity
  have := abs_nonneg p.1
  omega

lemma HE_fin (n : ℤ) : {p : ℤ × ℕ × Bool × Bool | HE p = n}.Finite :=
  ((Icc (-n) n ×ˢ (range (n.toNat + 1) ×ˢ (univ : Finset (Bool × Bool))) : Finset (ℤ × ℕ × Bool × Bool)) :
      Set (ℤ × ℕ × Bool × Bool)).toFinite.subset fun p hp => by
    have := HE_ge p
    simp only [Set.mem_setOf_eq] at hp
    have a1 := le_abs_self p.1; have a2 := neg_abs_le p.1
    simp only [coe_product, Set.mem_prod, coe_Icc, Set.mem_Icc, coe_range, Set.mem_Iio, coe_univ, Set.mem_univ,
      and_true]
    omega

noncomputable def HF : SummableFamily ℤ ℂ (ℤ × ℕ × Bool × Bool) :=
  monoFam HE HC 0 (fun p => by have := HE_ge p; have := abs_nonneg p.1; omega) HE_fin

lemma ιN_cj (j : ℤ) : ιN h6 (Chi0.cj j) = mono (6 * eD j false) 1 - mono (6 * eD j true) 1 := by
  unfold Chi0.cj
  rw [map_sub, ιN_Xpow, ιN_Xpow, Int.toNat_of_nonneg (Chi0.e1_nonneg j), Int.toNat_of_nonneg (Chi0.e2_nonneg j)]
  rfl

lemma ιN_tC (r u : ℕ) : ιN h6 (Chi0.tC r u) =
    mono (6 * Chi0.eC r u) ((-1) ^ u) + mono (6 * (Chi0.eC r u + (r + 1 + u))) ((-1) ^ u) := by
  unfold Chi0.tC
  rw [map_mul, map_mul, map_add, map_one, ιN_Xpow, ιN_Xpow, map_pow, map_neg, map_one, neg_one_pow_L,
    one_L, mono_mul, mul_add, mono_mul, mono_mul]
  exact congrArg₂ (· + ·) (mono_ext (by push_cast; ring) (by ring)) (mono_ext (by push_cast; ring) (by ring))

/-- the four monomials of `ιN (c_j t_{r(j),u})`. -/
lemma row_row_HF (j : ℤ) (u : ℕ) : uFam j u = hs (row (row HF j) u) := by
  rw [hs_eq_finset_sum univ (fun i hi => absurd (mem_univ i) hi)]
  simp only [uFam, psFam, ofSupp_apply, row_apply, HF, monoFam_apply, Fintype.sum_prod_type, Fintype.sum_bool]
  rw [map_mul, ιN_cj, ιN_tC]
  simp only [sub_mul, mul_add, mono_mul]
  have key : ∀ A B C D T1 T2 T3 T4 : L, T1 = -D → T2 = -C → T3 = B → T4 = A →
      A - C + (B - D) = T1 + T2 + (T3 + T4) := by intros; subst_vars; ring
  refine key _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_
  all_goals first
    | (rw [neg_mono]; exact mono_ext (by unfold HE; simp only [Bool.false_eq_true, if_false, if_true]; ring)
        (by unfold HC; simp))
    | exact mono_ext (by unfold HE; simp only [Bool.false_eq_true, if_false, if_true]; ring)
        (by unfold HC; simp)

lemma hs_row_HF (j : ℤ) : jFam j = hs (row HF j) := by
  have := hsum_fubini (row HF j) (uFam j) (row (row HF j)) (fun _ _ => rfl) (row_row_HF j)
  rw [this, hs_uFam]; rfl

/-- `ιN₆ ((q;q)_∞ χ₀) = Σ H`. -/
theorem hs_HF : hs HF = ιN h6 (MockTheta5.JTP.qfacInf * MockTheta5.Formal.chi0) := by
  rw [← hs_jFam]
  exact hsum_fubini HF jFam (row HF) (fun _ _ => rfl) hs_row_HF

/-! ## Reindexing to the eight cones -/

/-- `((b, δ, ε), (r, s)) ↦ (j, u, δ, ε)` with `j = r` (`b`) or `j = −1 − r`, `u = s`. -/
def σ8 : (Bool × Bool × Bool) × (ℕ × ℕ) ≃ ℤ × ℕ × Bool × Bool where
  toFun x := (if x.1.1 then (x.2.1 : ℤ) else -1 - (x.2.1 : ℤ), x.2.2, x.1.2.1, x.1.2.2)
  invFun p := ((decide (0 ≤ p.1), p.2.2.1, p.2.2.2), (if 0 ≤ p.1 then p.1.toNat else (-1 - p.1).toNat, p.2.1))
  left_inv x := by
    obtain ⟨⟨b, δ, ε⟩, r, s⟩ := x
    cases b
    · simp only [Bool.false_eq_true, if_false]
      rw [if_neg (by omega)]
      simp only [Prod.mk.injEq, decide_eq_false_iff_not, not_le, and_true]
      omega
    · simp
  right_inv p := by
    obtain ⟨j, u, δ, ε⟩ := p
    by_cases hj : 0 ≤ j
    · simp only [hj, decide_true, if_true, Prod.mk.injEq, and_true]; omega
    · simp only [hj, decide_false, Bool.false_eq_true, if_false, Prod.mk.injEq, and_true]; omega

/-- the cone parameters `(k, ex, ey)` of the `(b, δ, ε)` piece. -/
def cpar : Bool → Bool → Bool → ℕ × ℕ × ℕ
  | true, false, false => (0, 8, 4)
  | true, false, true => (1, 11, 5)
  | true, true, false => (1, 14, 4)
  | true, true, true => (2, 17, 5)
  | false, false, false => (9, 22, 10)
  | false, false, true => (12, 25, 11)
  | false, true, false => (4, 16, 10)
  | false, true, true => (7, 19, 11)

lemma eC_two (r u : ℕ) : 2 * (Chi0.eC r u : ℤ) = 2 * r + 6 * r * u + u * (3 * u + 5) := by
  have : 2 ∣ u * (3 * u + 5) := by
    rcases Nat.even_or_odd u with ⟨k, hk⟩ | ⟨k, hk⟩ <;> subst hk
    · exact ⟨k * (6 * k + 5), by ring⟩
    · exact ⟨(2 * k + 1) * (3 * k + 4), by ring⟩
  obtain ⟨c, hc⟩ := this
  have : Chi0.eC r u = r + 3 * r * u + c := by unfold Chi0.eC; rw [hc]; omega
  rw [this]; push_cast; rw [show (u : ℤ) * (3 * u + 5) = ((u * (3 * u + 5) : ℕ) : ℤ) by push_cast; ring, hc]
  push_cast; ring

lemma rj_pos (r : ℕ) : (Chi0.rj (r : ℤ) : ℤ) = 3 * r := by
  unfold Chi0.rj; rw [if_pos (by omega)]; omega
lemma rj_neg (r : ℕ) : (Chi0.rj (-1 - (r : ℤ)) : ℤ) = 3 * r + 2 := by
  unfold Chi0.rj; rw [if_neg (by omega)]; omega

lemma cancel2 {a b : ℤ} (h : 2 * a = 2 * b) : a = b := by omega

lemma neg_one_mul_mono (E : ℤ) (c : ℂ) : (-1 : L) * mono E c = mono E (-c) := by
  rw [neg_one_L, mono_mul]; simp

lemma one_mul_mono (E : ℤ) (c : ℂ) : (1 : L) * mono E c = mono E c := one_mul _

noncomputable def H8 : SummableFamily ℤ ℂ ((Bool × Bool × Bool) × (ℕ × ℕ)) := SummableFamily.Equiv σ8.symm HF

lemma row_H8 (b δ ε : Bool) :
    hs (row H8 (b, δ, ε)) = (if δ then -1 else 1) * Cp (cpar b δ ε).1 (cpar b δ ε).2.1 (cpar b δ ε).2.2 := by
  refine hsum_reindex _ _ (Equiv.refl _) _ fun p => ?_
  obtain ⟨r, s⟩ := p
  simp only [Equiv.refl_apply, row_apply, H8, SummableFamily.Equiv_toFun, Equiv.symm_symm, cpF, monoFam_apply,
    HF]
  have h2r := two_c2 (r : ℤ); have h2s := two_c2 (s : ℤ)
  cases b <;> cases δ <;> cases ε <;>
  · simp only [σ8, Equiv.coe_fn_mk, Bool.false_eq_true, if_false, if_true, cpar]
    simp only [neg_one_mul_mono, one_mul_mono]
    refine mono_ext ?_ (by unfold HC; simp)
    unfold HE cE eD
    simp only [Bool.false_eq_true, if_false, if_true]
    have hE1 := eC_two (Chi0.rj (r : ℤ)) s; rw [rj_pos] at hE1
    have hE2 := eC_two (Chi0.rj (-1 - (r : ℤ))) s; rw [rj_neg] at hE2
    try rw [rj_pos]
    try rw [rj_neg]
    apply cancel2
    push_cast
    first
      | linear_combination 6 * hE1 - 72 * h2r - 18 * h2s
      | linear_combination 6 * hE2 - 72 * h2r - 18 * h2s

/-- **the Bailey double sum as eight `f_{12,9,3}` cones**. -/
theorem qfac_chi0_cones : ιN h6 (MockTheta5.JTP.qfacInf * MockTheta5.Formal.chi0) =
    Cp 0 8 4 + Cp 1 11 5 - Cp 1 14 4 - Cp 2 17 5 - Cp 4 16 10 - Cp 7 19 11 + Cp 9 22 10 + Cp 12 25 11 := by
  have h1 : hs H8 = hs HF := by rw [hs_eq, hs_eq, H8, SummableFamily.hsum_equiv]
  rw [← hs_HF, ← h1, ← hs_rowFam, hs_eq_finset_sum univ (fun i hi => absurd (mem_univ i) hi)]
  simp only [rowFam_apply, Fintype.sum_prod_type, Fintype.sum_bool, row_H8, cpar, if_true, Bool.false_eq_true,
    if_false]
  ring

/-- **Garvan's Hecke form, cone version**: `(q;q)_∞ (χ₀ − 2) = −f(−q⁷,q²) + q f(−q¹³,q⁴) + q f(−q¹¹,q⁵) − q⁴ f(−q¹⁶,q⁸)`,
`f = f_{12,9,3}`, each full `f` written as its positive cone plus the reflected negative cone. -/
theorem qfac_chi0_garvan : ιN h6 (MockTheta5.JTP.qfacInf * MockTheta5.Formal.chi0) - 2 * ιN h6 MockTheta5.JTP.qfacInf =
    -(Cp 0 7 2 + Cp 15 26 13) + (Cp 1 13 4 + Cp 8 20 11) + (Cp 1 11 5 + Cp 9 22 10) - (Cp 4 16 8 + Cp 4 17 7) := by
  rw [qfac_chi0_cones, ← cone_identity]; ring

end MTC.Chi0L
