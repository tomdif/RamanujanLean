/-
# Bruhat decomposition restricted to `Γ₀(q)` (reusable)

For the box test function `ft P` of `SCSProof`, the `Γ₀(q)`-part of the `‖P‖²` sum,

    Σ_{γ ∈ SL₂(ℤ), q ∣ γ₁₀} I(γ),     I(γ) = ∫ ft · conj(ft ∘ γ),

is `Σ_{q ∣ c} T(c)` (`tsum_IγQ_eq`), i.e. only the Kloosterman layers `c ≡ 0 (mod q)` survive.
Since `‖T(c)‖` is bounded layer by layer, every bound for the full sum holds for the restricted
one, **uniformly in `q`**:

* `norm_tsum_IγQ_le_gK`: `‖Σ_{q|γ₁₀} I(γ)‖ ≤ 2∫⁻‖ft‖ + 2 Σ_{m ≤ K₂+1} ‖S(h,h;m)‖·64ε³/(mY)`;
* `norm_tsum_IγQ_le_gcd`: `‖Σ_{q|γ₁₀} I(γ)‖ ≤ C h^β ε³ Y^{−3/2−2δ}` (gcd-form Weil), `C` independent of `q`.

(`q = 0` gives `γ₁₀ = 0`, the parabolic subgroup; `q = 1` gives back `SCSSharp2.norm_tsum_Iγ_le_gcd`.)
-/
import RamanujanTau.SCSSharp2.KloostGcd

set_option autoImplicit false

namespace RamanujanTau.SCS2Coprime

open MeasureTheory Set Complex Finset
open UpperHalfPlane hiding I
open RamanujanTau.RankinError RamanujanTau.EisensteinReal RamanujanTau.EisensteinReal.Horo
open RamanujanTau.TauBound RamanujanTau.SCSProof RamanujanTau.SCSSharp2
open scoped MatrixGroups ENNReal Real ComplexConjugate

section
variable (P : Par)

open Classical in
/-- The `Γ₀(q)`-restricted Bruhat terms `[q ∣ γ₁₀] · I(γ)`. -/
noncomputable def IγQ (q : ℕ) (γ : SL(2, ℤ)) : ℂ := if (q : ℤ) ∣ γ 1 0 then Iγ P γ else 0

open Classical in
/-- The restricted layers `[q ∣ c] · T(c)`. -/
noncomputable def TlQ (q : ℕ) (c : ℤ) : ℂ := if (q : ℤ) ∣ c then Tl P c else 0

open Classical in
noncomputable def RtQ (q : ℕ) (x : ℤ × ℤ) : ℂ := if (q : ℤ) ∣ x.2 then Rt P x else 0

lemma summable_norm_Iγ : Summable fun γ => ‖Iγ P γ‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_Iγ_le P)
    (ENNReal.summable_toReal (tsum_Ip_ne_top P))

lemma norm_IγQ_le (q : ℕ) (γ : SL(2, ℤ)) : ‖IγQ P q γ‖ ≤ ‖Iγ P γ‖ := by
  unfold IγQ; split_ifs <;> simp

lemma summable_IγQ (q : ℕ) : Summable (IγQ P q) :=
  Summable.of_norm_bounded (summable_norm_Iγ P) (norm_IγQ_le P q)

lemma mul_T_zpow_10 (g : SL(2, ℤ)) (k : ℤ) : (g * ModularGroup.T ^ k) 1 0 = g 1 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma hasSum_right_TQ (q : ℕ) (g : SL(2, ℤ)) :
    HasSum (fun k : ℤ => IγQ P q (g * ModularGroup.T ^ k))
      (if (q : ℤ) ∣ g 1 0 then ∫ x, ff P x * conj (ft P (dsmul g x)) else 0) := by
  unfold IγQ
  simp_rw [mul_T_zpow_10]
  split_ifs
  · exact hasSum_right_T P g
  · exact hasSum_zero

lemma summable_slEquivQ (q : ℕ) :
    Summable fun x : copSet × ℤ => IγQ P q (mat x.1 * ModularGroup.T ^ x.2) :=
  (slEquiv.symm.summable_iff (f := IγQ P q)).2 (summable_IγQ P q)

lemma RtQ_val (q : ℕ) (p : copSet) : RtQ P q p.1 =
    if (q : ℤ) ∣ (mat p) 1 0 then ∫ x, ff P x * conj (ft P (dsmul (mat p) x)) else 0 := by
  unfold RtQ; rw [Rt_val, mat_apply_10]

lemma support_RtQ (q : ℕ) :
    Function.support (RtQ P q) ⊆ Set.range (Subtype.val : copSet → ℤ × ℤ) := by
  intro x hx
  apply support_Rt P
  intro h; apply hx; unfold RtQ; rw [h]; simp

lemma tsum_IγQ_eq_RtQ (q : ℕ) : ∑' γ, IγQ P q γ = ∑' x, RtQ P q x := by
  rw [← slEquiv.symm.tsum_eq (IγQ P q)]
  change ∑' x : copSet × ℤ, IγQ P q (mat x.1 * ModularGroup.T ^ x.2) = _
  rw [(summable_slEquivQ P q).tsum_prod' (fun p => (summable_slEquivQ P q).comp_injective
    (Prod.mk_right_injective p))]
  rw [← Subtype.val_injective.tsum_eq (support_RtQ P q)]
  exact tsum_congr fun p => by rw [RtQ_val]; exact (hasSum_right_TQ P q (mat p)).tsum_eq

lemma norm_RtQ_le (q : ℕ) (x : ℤ × ℤ) : ‖RtQ P q x‖ ≤ ‖Rt P x‖ := by
  unfold RtQ; split_ifs <;> simp

lemma summable_RtQ (q : ℕ) : Summable (RtQ P q) := by
  have := (Subtype.val_injective.summable_iff (f := RtQ P q) (fun x hx =>
    Function.notMem_support.1 (fun h => hx (support_RtQ P q h)))).1
  refine this ?_
  have h2 := (summable_slEquivQ P q).prod
  exact h2.congr fun p => by
    show _ = RtQ P q p.1
    rw [RtQ_val]; exact (hasSum_right_TQ P q (mat p)).tsum_eq

lemma summable_swapQ (q : ℕ) : Summable fun y : ℤ × ℤ => RtQ P q (y.2, y.1) :=
  ((Equiv.prodComm ℤ ℤ).summable_iff (f := RtQ P q)).2 (summable_RtQ P q)

/-- **Restricted Bruhat sum = restricted layers**: `Σ_{q|γ₁₀} I(γ) = Σ_{q|c} T(c)`. -/
theorem tsum_IγQ_eq (q : ℕ) : ∑' γ, IγQ P q γ = ∑' c, TlQ P q c := by
  rw [tsum_IγQ_eq_RtQ, ← (Equiv.prodComm ℤ ℤ).tsum_eq (RtQ P q)]
  change ∑' y : ℤ × ℤ, RtQ P q (y.2, y.1) = _
  rw [(summable_swapQ P q).tsum_prod' (fun c => (summable_swapQ P q).comp_injective
    (Prod.mk_right_injective c))]
  refine tsum_congr fun c => ?_
  unfold TlQ Tl RtQ
  split_ifs with h
  · rfl
  · simp

lemma summable_TlQ (q : ℕ) : Summable (TlQ P q) := by
  have h := (summable_swapQ P q).prod
  refine h.congr fun c => ?_
  unfold TlQ Tl RtQ
  split_ifs with hc
  · rfl
  · simp

lemma norm_TlQ_le_Tl (q : ℕ) (c : ℤ) : ‖TlQ P q c‖ ≤ ‖Tl P c‖ := by
  unfold TlQ; split_ifs <;> simp

lemma norm_TlQ_zero (q : ℕ) : ‖TlQ P q 0‖ ≤ 2 * (∫⁻ x, ‖ft P x‖ₑ).toReal :=
  (norm_TlQ_le_Tl P q 0).trans (norm_Tl_zero P)

lemma norm_TlQ_le (q : ℕ) (c : ℤ) (hc : c ≠ 0) : ‖TlQ P q c‖ ≤ gK P c.natAbs :=
  (norm_TlQ_le_Tl P q c).trans (norm_Tl_le P c hc)

lemma TlQ_zero_of_large (q : ℕ) (c : ℤ) (hc : c ≠ 0) (hcY : 2 ≤ |(c : ℝ)| * P.Y) :
    TlQ P q c = 0 := by
  unfold TlQ; rw [Tl_zero_of_large P c hc hcY]; simp

/-- The layer sum bound. -/
theorem norm_tsum_IγQ_le_gK (q : ℕ) :
    ‖∑' γ, IγQ P q γ‖ ≤ 2 * (∫⁻ x, ‖ft P x‖ₑ).toReal +
      2 * ∑ m ∈ Finset.range (K2 P + 2), gK P m := by
  set X := (∫⁻ x, ‖ft P x‖ₑ).toReal
  have hX : 0 ≤ X := ENNReal.toReal_nonneg
  rw [tsum_IγQ_eq]
  have hsT := summable_TlQ P q
  -- finite support
  have hsupp : ∀ c : ℤ, K2 P < c.natAbs → TlQ P q c = 0 := by
    intro c hc
    have hc0 : c ≠ 0 := by intro h; rw [h] at hc; simp at hc
    refine TlQ_zero_of_large P q c hc0 ?_
    rw [← natAbs_cast]; exact large_of_gt P _ hc
  set H : ℕ → ℝ := fun n => if n ≤ K2 P then (if n = 0 then 2 * X else 0) + gK P n + gK P (n + 1)
    else 0
  have hTH : ∀ n : ℕ, ‖TlQ P q n‖ + ‖TlQ P q (-(n + 1 : ℤ))‖ ≤ H n := by
    intro n
    simp only [H]
    split_ifs with hn hn0
    · subst hn0
      have h1 := norm_TlQ_zero P q
      have h2 := norm_TlQ_le P q (-(0 + 1 : ℤ)) (by norm_num)
      simp only [Nat.cast_zero] at h1 ⊢
      have : (-(0 + 1 : ℤ)).natAbs = 0 + 1 := by norm_num
      rw [this] at h2
      linarith [gK_nonneg P 0]
    · have h1 := norm_TlQ_le P q (n : ℤ) (by exact_mod_cast hn0)
      have h2 := norm_TlQ_le P q (-(n + 1 : ℤ)) (by omega)
      have e1 : ((n : ℤ)).natAbs = n := Int.natAbs_natCast n
      have e2 : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
      rw [e1] at h1; rw [e2] at h2
      linarith
    · have h1 : TlQ P q n = 0 := hsupp n (by rw [Int.natAbs_natCast]; omega)
      have h2 : TlQ P q (-(n + 1 : ℤ)) = 0 := hsupp _ (by omega)
      rw [h1, h2]; simp
  have hHsupp : ∀ n ∉ Finset.range (K2 P + 1), H n = 0 := by
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    simp only [H]; rw [if_neg (by omega)]
  have hsN : Summable fun n : ℕ => ‖TlQ P q n‖ + ‖TlQ P q (-(n + 1 : ℤ))‖ :=
    hsT.norm.nat_add_neg_add_one
  calc ‖∑' c, TlQ P q c‖ ≤ ∑' c, ‖TlQ P q c‖ := norm_tsum_le_tsum_norm hsT.norm
    _ = ∑' n : ℕ, (‖TlQ P q n‖ + ‖TlQ P q (-(n + 1 : ℤ))‖) := (tsum_nat_add_neg_add_one hsT.norm).symm
    _ ≤ ∑' n : ℕ, H n := hsN.tsum_le_tsum hTH (summable_of_ne_finset_zero hHsupp)
    _ = ∑ n ∈ Finset.range (K2 P + 1), H n := tsum_eq_sum hHsupp
    _ ≤ 2 * X + 2 * ∑ m ∈ Finset.range (K2 P + 2), gK P m := by
        have hH : ∀ n ∈ Finset.range (K2 P + 1), H n =
            (if n = 0 then 2 * X else 0) + gK P n + gK P (n + 1) := by
          intro n hn
          simp only [H]; rw [if_pos (by simpa [Nat.lt_succ_iff] using hn)]
        rw [Finset.sum_congr rfl hH, Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_ite_eq' (Finset.range (K2 P + 1)) 0]
        rw [if_pos (by simp)]
        have hA : ∑ n ∈ Finset.range (K2 P + 1), gK P n ≤
            ∑ m ∈ Finset.range (K2 P + 2), gK P m :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
            (fun m _ _ => gK_nonneg P m)
        have hB : ∑ n ∈ Finset.range (K2 P + 1), gK P (n + 1) ≤
            ∑ m ∈ Finset.range (K2 P + 2), gK P m := by
          rw [Finset.sum_range_succ' (fun m => gK P m) (K2 P + 1)]
          linarith [gK_nonneg P 0]
        linarith


end

set_option maxHeartbeats 1000000 in
/-- **`‖P‖²`-bound (Weil, gcd form)**: `‖Σ_γ I(γ)‖ ≤ C h^β ε³ Y^{−3/2−2δ}`. -/
theorem norm_tsum_IγQ_le_gcd (δ β : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hβ : 0 < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : Par) (q : ℕ), 1 ≤ P.h →
      ‖∑' γ, IγQ P q γ‖ ≤ C * (P.h : ℝ) ^ β * P.ε ^ 3 * P.Y ^ (-(3 / 2 : ℝ) - 2 * δ) := by
  obtain ⟨A, hA0, hA⟩ := norm_kloosterman_hh_gcd_le δ hδ
  obtain ⟨Cd, hCd1, hCd⟩ := card_divisors_le_rpow β hβ
  refine ⟨32 + 128 * A * Cd * 25 * (1 + 1 / δ), by positivity, fun P q hh => ?_⟩
  have hY := P.hY; have hY1 := P.hY1; have hε := P.hε
  have hhR : (1 : ℝ) ≤ P.h := by exact_mod_cast hh
  have h1 := norm_tsum_IγQ_le_gK P q
  -- the `∫⁻ ‖ft‖` term
  have hX : (∫⁻ q, ‖ft P q‖ₑ).toReal ≤ 16 * P.ε ^ 3 / P.Y := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (lintegral_ft_le P)
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  -- `Y^{-1} ≤ Y^{-3/2-2δ}`
  have hYpow : P.Y ^ (-(1 : ℝ)) ≤ P.Y ^ (-(3 / 2 : ℝ) - 2 * δ) :=
    Real.rpow_le_rpow_of_exponent_ge hY hY1 (by linarith)
  have hYinv : 1 / P.Y = P.Y ^ (-(1 : ℝ)) := by rw [Real.rpow_neg_one, one_div]
  have hhβ : (1 : ℝ) ≤ (P.h : ℝ) ^ β := Real.one_le_rpow hhR hβ.le
  -- the Kloosterman terms
  have hg : ∀ m ∈ Finset.range (K2 P + 2), SCSProof.gK P m ≤
      (A * (64 * P.ε ^ 3 / P.Y)) * (Real.sqrt (Nat.gcd P.h m) *
        (if m = 0 then 0 else (m : ℝ) ^ (1 / 2 + δ) / m)) := by
    intro m _
    unfold SCSProof.gK
    split_ifs with hm0
    · subst hm0; simp [kloosterman_zero_mod]
    · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.2 hm0
      have hk := hA P.h m hh hm1
      have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
      calc ‖kloosterman P.h P.h m‖ * (64 * P.ε ^ 3 / (m * P.Y))
          ≤ (A * Real.sqrt (Nat.gcd P.h m) * (m : ℝ) ^ (1 / 2 + δ)) * (64 * P.ε ^ 3 / (m * P.Y)) := by
            gcongr
        _ = _ := by field_simp
  have hsum0 := Finset.sum_le_sum hg
  rw [← Finset.mul_sum] at hsum0
  have hG := sum_gcd_le δ hδ P.h hh (K2 P)
  have hcoef0 : 0 ≤ A * (64 * P.ε ^ 3 / P.Y) := by positivity
  have hsum : ∑ m ∈ Finset.range (K2 P + 2), SCSProof.gK P m ≤
      (A * Cd * (P.h : ℝ) ^ β * (64 * P.ε ^ 3 / P.Y)) *
        (((K2 P : ℝ) + 2) ^ (1 / 2 + δ) * (1 + Real.log (K2 P + 1))) := by
    have hL0 : 0 ≤ ((K2 P : ℝ) + 2) ^ (1 / 2 + δ) * (1 + Real.log (K2 P + 1)) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ K2 P + 1 by
        have : (0 : ℝ) ≤ K2 P := Nat.cast_nonneg _
        linarith)
      positivity
    calc _ ≤ _ := hsum0
      _ ≤ (A * (64 * P.ε ^ 3 / P.Y)) * ((#P.h.divisors : ℝ) *
            (((K2 P : ℝ) + 2) ^ (1 / 2 + δ) * (1 + Real.log (K2 P + 1)))) := by gcongr
      _ ≤ (A * (64 * P.ε ^ 3 / P.Y)) * ((Cd * (P.h : ℝ) ^ β) *
            (((K2 P : ℝ) + 2) ^ (1 / 2 + δ) * (1 + Real.log (K2 P + 1)))) := by
          gcongr; exact hCd P.h hh
      _ = _ := by ring
  have hS := sum_rpow_div_le δ hδ (K2 P)
  -- `K₂ + 2 ≤ 5/Y`
  have hK : (K2 P : ℝ) + 2 ≤ 5 / P.Y := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 / P.Y by positivity)
    have h3 : 3 ≤ 3 / P.Y := by rw [le_div_iff₀ hY]; linarith
    unfold K2
    have : (5 : ℝ) / P.Y = 2 / P.Y + 3 / P.Y := by ring
    linarith
  have hK1 : (1 : ℝ) ≤ 5 / P.Y := by rw [le_div_iff₀ hY]; linarith
  have hlog : Real.log ((K2 P : ℝ) + 1) ≤ (5 / P.Y) ^ δ / δ := by
    refine (Real.log_le_rpow_div (by positivity) hδ).trans ?_
    gcongr; linarith
  have hpow1 : ((K2 P : ℝ) + 2) ^ (1 / 2 + δ) ≤ (5 / P.Y) ^ (1 / 2 + δ) := by
    gcongr
  have hS' : ((K2 P : ℝ) + 2) ^ (1 / 2 + δ) * (1 + Real.log (K2 P + 1)) ≤
      25 * (1 + 1 / δ) * P.Y ^ (-(1 / 2 : ℝ) - 2 * δ) := by
    have e1 : (5 / P.Y) ^ (1 / 2 + δ) * (5 / P.Y) ^ δ = (5 / P.Y) ^ (1 / 2 + 2 * δ) := by
      rw [← Real.rpow_add (by positivity)]; ring_nf
    have e2 : (5 / P.Y) ^ (1 / 2 + 2 * δ) = (5 : ℝ) ^ (1 / 2 + 2 * δ) * P.Y ^ (-(1 / 2 : ℝ) - 2 * δ) := by
      rw [Real.div_rpow (by norm_num) hY.le, div_eq_mul_inv, ← Real.rpow_neg hY.le]
      ring_nf
    have h5 : (5 : ℝ) ^ (1 / 2 + 2 * δ) ≤ 25 := by
      calc (5 : ℝ) ^ (1 / 2 + 2 * δ) ≤ (5 : ℝ) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 25 := by norm_num
    have hpowδ : 1 ≤ (5 / P.Y) ^ δ := Real.one_le_rpow hK1 hδ.le
    have hYp : 0 < P.Y ^ (-(1 / 2 : ℝ) - 2 * δ) := Real.rpow_pos_of_pos hY _
    calc ((K2 P : ℝ) + 2) ^ (1 / 2 + δ) * (1 + Real.log (K2 P + 1))
        ≤ (5 / P.Y) ^ (1 / 2 + δ) * ((5 / P.Y) ^ δ * (1 + 1 / δ)) := by
          gcongr
          · have := Real.log_nonneg (show (1 : ℝ) ≤ K2 P + 1 by
              have : (0 : ℝ) ≤ K2 P := Nat.cast_nonneg _
              linarith)
            linarith
          · calc 1 + Real.log ((K2 P : ℝ) + 1) ≤ 1 + (5 / P.Y) ^ δ / δ := by linarith
              _ ≤ (5 / P.Y) ^ δ + (5 / P.Y) ^ δ / δ := by linarith
              _ = (5 / P.Y) ^ δ * (1 + 1 / δ) := by ring
      _ = (5 / P.Y) ^ (1 / 2 + 2 * δ) * (1 + 1 / δ) := by rw [← e1]; ring
      _ ≤ 25 * P.Y ^ (-(1 / 2 : ℝ) - 2 * δ) * (1 + 1 / δ) := by
          rw [e2]; gcongr
      _ = 25 * (1 + 1 / δ) * P.Y ^ (-(1 / 2 : ℝ) - 2 * δ) := by ring
  have hYsplit : 1 / P.Y * P.Y ^ (-(1 / 2 : ℝ) - 2 * δ) = P.Y ^ (-(3 / 2 : ℝ) - 2 * δ) := by
    rw [hYinv, ← Real.rpow_add hY]; ring_nf
  have hYp3 : 0 ≤ P.Y ^ (-(3 / 2 : ℝ) - 2 * δ) := (Real.rpow_pos_of_pos hY _).le
  have hfin : 2 * ∑ m ∈ Finset.range (K2 P + 2), SCSProof.gK P m ≤
      128 * A * Cd * 25 * (1 + 1 / δ) * (P.h : ℝ) ^ β * P.ε ^ 3 *
        P.Y ^ (-(3 / 2 : ℝ) - 2 * δ) := by
    have hcoef : 0 ≤ A * Cd * (P.h : ℝ) ^ β * (64 * P.ε ^ 3 / P.Y) := by positivity
    calc 2 * ∑ m ∈ Finset.range (K2 P + 2), SCSProof.gK P m
        ≤ 2 * ((A * Cd * (P.h : ℝ) ^ β * (64 * P.ε ^ 3 / P.Y)) * (25 * (1 + 1 / δ) *
            P.Y ^ (-(1 / 2 : ℝ) - 2 * δ))) := by
          gcongr; exact hsum.trans (mul_le_mul_of_nonneg_left hS' hcoef)
      _ = 128 * A * Cd * 25 * (1 + 1 / δ) * (P.h : ℝ) ^ β * P.ε ^ 3 *
            (1 / P.Y * P.Y ^ (-(1 / 2 : ℝ) - 2 * δ)) := by ring
      _ = _ := by rw [hYsplit]
  have hfirst : 2 * (∫⁻ q, ‖ft P q‖ₑ).toReal ≤
      32 * (P.h : ℝ) ^ β * P.ε ^ 3 * P.Y ^ (-(3 / 2 : ℝ) - 2 * δ) := by
    have : 2 * (16 * P.ε ^ 3 / P.Y) = 32 * P.ε ^ 3 * P.Y ^ (-(1 : ℝ)) := by rw [← hYinv]; ring
    calc 2 * (∫⁻ q, ‖ft P q‖ₑ).toReal ≤ 2 * (16 * P.ε ^ 3 / P.Y) := by linarith
      _ = 32 * P.ε ^ 3 * P.Y ^ (-(1 : ℝ)) := this
      _ ≤ 32 * P.ε ^ 3 * P.Y ^ (-(3 / 2 : ℝ) - 2 * δ) := by gcongr
      _ ≤ 32 * (P.h : ℝ) ^ β * P.ε ^ 3 * P.Y ^ (-(3 / 2 : ℝ) - 2 * δ) := by
          have : 0 ≤ P.ε ^ 3 * P.Y ^ (-(3 / 2 : ℝ) - 2 * δ) := by positivity
          nlinarith [hhβ]
  calc ‖∑' γ, IγQ P q γ‖ ≤ _ := h1
    _ ≤ 32 * (P.h : ℝ) ^ β * P.ε ^ 3 * P.Y ^ (-(3 / 2 : ℝ) - 2 * δ) +
          128 * A * Cd * 25 * (1 + 1 / δ) * (P.h : ℝ) ^ β * P.ε ^ 3 *
            P.Y ^ (-(3 / 2 : ℝ) - 2 * δ) :=
        add_le_add hfirst hfin
    _ = _ := by ring

end RamanujanTau.SCS2Coprime
