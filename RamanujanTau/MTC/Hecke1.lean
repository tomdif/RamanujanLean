/-
# The Hecke side at the MTC₁ point: `f_{3,7,3}(x₁, y₁) = (q;q)_∞ f₁` (HM (8.13))

Exactly as `Hecke373` with `105` replaced by `189`: the terms with `r − s` odd cancel, and the even terms are Andrews'
Hecke sum `Σ_{n≥0} Σ_{|j|≤n} (−1)^j Q^{n(5n+3)/2 − j²}(1 − Q^{2n+1})` (`MockTheta5F1Pair`).
-/
import RamanujanTau.MTC.Hecke373
import RamanujanTau.MockTheta5F1Pair

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset

/-- the exponent `42(3C(r,2) + 7rs + 3C(s,2)) + 189(r + s)`. -/
def E73₁ (r s : ℤ) : ℤ := 42 * (3 * c2 r + 7 * r * s + 3 * c2 s) + 189 * (r + s)

lemma E73_bound₁ {r s : ℤ} (h : reg r s) : 21 * (|r| + |s|) ≤ E73₁ r s := by
  unfold E73₁
  have h1 := two_c2 r; have h2 := two_c2 s
  rcases h with ⟨hr, hs⟩ | ⟨hr, hs⟩
  · rw [abs_of_nonneg hr, abs_of_nonneg hs]
    nlinarith [mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg hs hs]
  · rw [abs_of_neg hr, abs_of_neg hs]
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ -r) (by linarith : (0 : ℤ) ≤ -s),
      mul_nonneg (by linarith : (0 : ℤ) ≤ -r - 1) (by linarith : (0 : ℤ) ≤ -r),
      mul_nonneg (by linarith : (0 : ℤ) ≤ -s - 1) (by linarith : (0 : ℤ) ≤ -s)]

noncomputable def t73₁ (p : ℤ × ℤ) : L := if reg p.1 p.2 then mono (E73₁ p.1 p.2) (C73 p.1 p.2) else 0

lemma t73_lb₁ (p : ℤ × ℤ) (n : ℤ) (hn : (t73₁ p).coeff n ≠ 0) : reg p.1 p.2 ∧ n = E73₁ p.1 p.2 := by
  unfold t73₁ at hn
  split_ifs at hn with h
  · exact ⟨h, coeff_mono_ne hn⟩
  · simp at hn

lemma t73_hD₁ (p : ℤ × ℤ) (n : ℤ) (hn : n < 0) : (t73₁ p).coeff n = 0 := by
  by_contra h
  obtain ⟨hr, rfl⟩ := t73_lb₁ p n h
  have := E73_bound₁ hr; have := abs_nonneg p.1; have := abs_nonneg p.2; omega

noncomputable def T73₁ : SummableFamily ℤ ℂ (ℤ × ℤ) :=
  ofSupp t73₁ 0 (fun p n hn => t73_hD₁ p n hn)
    (fun n => box_fin n _ fun p hp => by obtain ⟨hr, rfl⟩ := t73_lb₁ p n hp; exact E73_bound₁ hr)

/-! ## The odd part cancels -/

noncomputable def todd₁ (p : ℤ × ℤ) : L := if (p.1 - p.2) % 2 = 1 then t73₁ p else 0

noncomputable def Todd₁ : SummableFamily ℤ ℂ (ℤ × ℤ) :=
  ofSupp todd₁ 0 (fun p n hn => by
    unfold todd₁
    split_ifs with h
    · exact t73_hD₁ p n hn
    · simp)
    (fun n => box_fin n _ fun p hp => by
      unfold todd₁ at hp
      split_ifs at hp
      · obtain ⟨hr, rfl⟩ := t73_lb₁ p n hp; exact E73_bound₁ hr
      · simp at hp)

lemma todd_swap₁ (p : ℤ × ℤ) : todd₁ (p.2, p.1) = -1 * todd₁ p := by
  obtain ⟨r, s⟩ := p
  unfold todd₁ t73₁
  try dsimp only
  by_cases ho : (r - s) % 2 = 1
  · have ho' : (s - r) % 2 = 1 := by omega
    rw [if_pos ho', if_pos ho]
    by_cases hr : reg r s
    · have hr' : reg s r := by unfold reg at hr ⊢; omega
      rw [if_pos hr', if_pos hr, mono_ext (show E73₁ s r = E73₁ r s by unfold E73₁; ring) (C73_swap ho hr),
        ← neg_mono_h]
      ring
    · have hr' : ¬ reg s r := by unfold reg at hr ⊢; omega
      rw [if_neg hr', if_neg hr, mul_zero]
  · have ho' : ¬ (s - r) % 2 = 1 := by omega
    rw [if_neg ho', if_neg ho, mul_zero]

lemma hs_Todd₁ : hs Todd₁ = 0 :=
  eq_zero_of_eq_neg' (hsum_reindex Todd₁ Todd₁ (Equiv.prodComm ℤ ℤ) (-1) fun p => todd_swap₁ p)

/-! ## The even part is Andrews' Hecke sum -/

noncomputable def r2₁ (q : ℕ × (ℤ × Fin 2)) : L :=
  if |q.2.1| ≤ (q.1 : ℤ) then
    (if q.2.2 = 0 then mono (84 * (5 * (q.1 : ℤ) ^ 2 + 3 * q.1) - 168 * q.2.1 ^ 2) ((-1) ^ q.2.1)
     else mono (84 * (5 * (q.1 : ℤ) ^ 2 + 7 * q.1 + 2) - 168 * q.2.1 ^ 2) (-(-1) ^ q.2.1))
  else 0

lemma r2_lb₁ (q : ℕ × (ℤ × Fin 2)) (n : ℤ) (hn : (r2₁ q).coeff n ≠ 0) :
    84 * (q.1 : ℤ) ≤ n ∧ |q.2.1| ≤ (q.1 : ℤ) := by
  unfold r2₁ at hn
  split_ifs at hn with h1 h2
  · have := coeff_mono_ne hn
    have hj : q.2.1 ^ 2 ≤ (q.1 : ℤ) ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    exact ⟨by nlinarith [sq_nonneg (q.1 : ℤ)], h1⟩
  · have := coeff_mono_ne hn
    have hj : q.2.1 ^ 2 ≤ (q.1 : ℤ) ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    exact ⟨by nlinarith [sq_nonneg (q.1 : ℤ)], h1⟩
  · simp at hn

noncomputable def R2₁ : SummableFamily ℤ ℂ (ℕ × (ℤ × Fin 2)) :=
  ofSupp r2₁ 0 (fun q n hn => by
      by_contra h
      have := (r2_lb₁ q n h).1
      have : (0 : ℤ) ≤ q.1 := by positivity
      omega)
    (fun n => ((Finset.range (n.toNat + 1) ×ˢ (Finset.Icc (-n) n ×ˢ Finset.univ) :
        Finset (ℕ × (ℤ × Fin 2))) : Set _).toFinite.subset fun q hq => by
      obtain ⟨h1, h2⟩ := r2_lb₁ q n hq
      have a1 := le_abs_self q.2.1; have a2 := neg_abs_le q.2.1
      simp only [Finset.coe_product, Set.mem_prod, Finset.coe_range, Set.mem_Iio, Finset.coe_Icc,
        Set.mem_Icc, Finset.coe_univ, Set.mem_univ, and_true]
      omega)

lemma t73_psi₁ (q : ℕ × (ℤ × Fin 2)) : t73₁ (psi q) = r2₁ q := by
  obtain ⟨n, j, p⟩ := q
  have h1 := two_c2 ((n : ℤ) + j); have h2 := two_c2 ((n : ℤ) - j)
  have h3 := two_c2 (j - n - 1); have h4 := two_c2 (-j - n - 1)
  fin_cases p
  · show (if reg ((n : ℤ) + j) ((n : ℤ) - j) then mono (E73₁ ((n : ℤ) + j) ((n : ℤ) - j))
        (C73 ((n : ℤ) + j) ((n : ℤ) - j)) else 0) =
      (if |j| ≤ (n : ℤ) then mono (84 * (5 * (n : ℤ) ^ 2 + 3 * n) - 168 * j ^ 2) ((-1) ^ j) else 0)
    by_cases hj : |j| ≤ (n : ℤ)
    · have := abs_le.mp hj
      rw [if_pos (show reg _ _ from Or.inl ⟨by omega, by omega⟩), if_pos hj]
      refine mono_ext (by unfold E73₁; linear_combination 63 * h1 + 63 * h2) ?_
      unfold C73
      rw [if_pos (show (0 : ℤ) ≤ (n : ℤ) + j by omega)]
      simp only [Z_neg']
      zsimp
      exact Z_mod (by omega)
    · rw [if_neg (show ¬ reg ((n : ℤ) + j) ((n : ℤ) - j) by unfold reg; intro h; apply hj; rw [abs_le]; omega), if_neg hj]
  · show (if reg (j - n - 1) (-j - n - 1) then mono (E73₁ (j - n - 1) (-j - n - 1))
        (C73 (j - n - 1) (-j - n - 1)) else 0) =
      (if |j| ≤ (n : ℤ) then mono (84 * (5 * (n : ℤ) ^ 2 + 7 * n + 2) - 168 * j ^ 2) (-(-1) ^ j) else 0)
    by_cases hj : |j| ≤ (n : ℤ)
    · have := abs_le.mp hj
      rw [if_pos (show reg _ _ from Or.inr ⟨by omega, by omega⟩), if_pos hj]
      refine mono_ext (by unfold E73₁; linear_combination 63 * h3 + 63 * h4) ?_
      unfold C73
      rw [if_neg (show ¬ (0 : ℤ) ≤ j - n - 1 by omega)]
      simp only [Z_neg']
      zsimp
      exact Z_mod (by omega)
    · rw [if_neg (show ¬ reg (j - n - 1) (-j - n - 1) by unfold reg; intro h; apply hj; rw [abs_le]; omega), if_neg hj]

lemma todd_psi₁ (q : ℕ × (ℤ × Fin 2)) : todd₁ (psi q) = 0 := by
  unfold todd₁
  rw [if_neg (show ¬ ((psi q).1 - (psi q).2) % 2 = 1 by rw [psi_diff]; omega)]

lemma T73_split₁ : T73₁ = R2₁.embDomain psiE + Todd₁ := by
  ext ⟨r, s⟩ : 1
  rw [SummableFamily.add_apply]
  show t73₁ (r, s) = _ + todd₁ (r, s)
  by_cases ho : (r - s) % 2 = 1
  · rw [SummableFamily.embDomain_notin_range (s := R2₁) (f := psiE) (b := (r, s)) (by
      rintro ⟨q, hq⟩
      have := psi_diff q
      rw [show psi q = (r, s) from hq] at this
      simp only at this; omega)]
    unfold todd₁
    rw [if_pos ho, zero_add]
  · obtain ⟨q, hq⟩ : ∃ q, psiE q = (r, s) := by
      by_cases hu : 0 ≤ r + s
      · refine ⟨(((r + s) / 2).toNat, (r - s) / 2, 0), ?_⟩
        show (((((r + s) / 2).toNat : ℕ) : ℤ) + (r - s) / 2, ((((r + s) / 2).toNat : ℕ) : ℤ) - (r - s) / 2) = (r, s)
        rw [Prod.mk.injEq]
        omega
      · refine ⟨(((-(r + s)) / 2 - 1).toNat, (r - s) / 2, 1), ?_⟩
        show ((r - s) / 2 - (((-(r + s)) / 2 - 1).toNat : ℕ) - 1,
          -((r - s) / 2) - (((-(r + s)) / 2 - 1).toNat : ℕ) - 1) = (r, s)
        rw [Prod.mk.injEq]
        omega
    rw [← hq, SummableFamily.embDomain_image]
    show t73₁ (psi q) = r2₁ q + todd₁ (psi q)
    rw [t73_psi₁, todd_psi₁, add_zero]

lemma hs_T73₁ : hs T73₁ = hs R2₁ := by
  rw [T73_split₁, hs_eq, SummableFamily.hsum_add, SummableFamily.hsum_embDomain, ← hs_eq, ← hs_eq, hs_Todd₁,
    add_zero]

/-! ## Rows of `R2₁` and the Hecke sum -/

lemma heckeF1_coeff_lt₁ (n k : ℕ) (hk : k < n) : PowerSeries.coeff k (MockTheta5.Bailey.heckeF1 n) = 0 := by
  unfold MockTheta5.Bailey.heckeF1
  rw [mul_assoc, PowerSeries.coeff_X_pow_mul', if_neg]
  have : n ≤ n ^ 2 := Nat.le_self_pow two_ne_zero n
  omega

noncomputable def hkF₁ : SummableFamily ℤ ℂ ℕ :=
  ofSupp (fun n => ιN h168 (MockTheta5.Bailey.heckeF1 n)) 0 (fun n m hm => ιN_coeff_neg h168 _ hm)
    (fun m => (Set.finite_Iic m.toNat).subset fun n hn => by
      simp only [Set.mem_setOf_eq] at hn
      simp only [Set.mem_Iic]
      rcases lt_or_ge m 0 with h | h
      · exact absurd (ιN_coeff_neg h168 _ h) hn
      · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = k := ⟨m.toNat, by omega⟩
        rw [ιN_coeff_nat] at hn
        split_ifs at hn with hd
        · by_contra hlt
          apply hn
          rw [heckeF1_coeff_lt₁ n (k / 168) (by have := Nat.div_le_self k 168; omega)]
          simp
        · simp at hn)

lemma hs_hkF₁ : hs hkF₁ = ιN h168 MockTheta5.JTP.heckeSumF1 := by
  ext m
  rw [hs, SummableFamily.coeff_hsum]
  rcases lt_or_ge m 0 with hm | hm
  · rw [ιN_coeff_neg h168 _ hm]
    exact finsum_eq_zero_of_forall_eq_zero fun n => ιN_coeff_neg h168 _ hm
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = k := ⟨m.toNat, by omega⟩
    simp only [hkF₁, ofSupp_apply, ιN_coeff_nat]
    split_ifs with hd
    · rw [MockTheta5.JTP.heckeSumF1, PowerSeries.coeff_mk, map_sum, Int.cast_sum,
        finsum_eq_sum_of_support_subset (s := Finset.range (k / 168 + 1))]
      intro n hn
      rw [Function.mem_support] at hn
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra hlt
      apply hn
      rw [heckeF1_coeff_lt₁ n (k / 168) (by omega)]
      simp
    · simp

lemma row_R2₁ (n : ℕ) : ιN h168 (MockTheta5.Bailey.heckeF1 n) = hs (row R2₁ n) := by
  rw [hs_eq_finset_sum (Finset.Icc (-(n : ℤ)) n ×ˢ Finset.univ) (fun jp hjp => by
    simp only [row_apply]
    show r2₁ (n, jp) = 0
    unfold r2₁
    rw [if_neg]
    intro h
    apply hjp
    simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_univ, and_true]
    exact abs_le.mp h)]
  rw [Finset.sum_product]
  simp only [row_apply, Fin.sum_univ_two]
  unfold MockTheta5.Bailey.heckeF1
  rw [map_mul, map_mul, ιN_Vth h168, map_sub, map_one, ιN_Xpow, ιN_Xpow, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : |j| ≤ (n : ℤ) := abs_le.mpr (Finset.mem_Icc.mp hj)
  show _ = r2₁ (n, j, 0) + r2₁ (n, j, 1)
  rw [show r2₁ (n, j, 0) = mono (84 * (5 * (n : ℤ) ^ 2 + 3 * n) - 168 * j ^ 2) ((-1) ^ j) from by
      show (if |j| ≤ (n : ℤ) then (if (0 : Fin 2) = 0 then _ else _) else 0) = _
      rw [if_pos hjn]; rfl,
    show r2₁ (n, j, 1) = mono (84 * (5 * (n : ℤ) ^ 2 + 7 * n + 2) - 168 * j ^ 2) (-(-1) ^ j) from by
      show (if |j| ≤ (n : ℤ) then (if (1 : Fin 2) = 0 then _ else _) else 0) = _
      rw [if_pos hjn]; rfl]
  rw [mul_sub, mul_one]
  simp only [mono_mul]
  rw [sub_eq_add_neg, neg_mono_h]
  have ht := two_triF n
  have ht' : (2 : ℤ) * (MockTheta5.Bailey.triF n : ℤ) = n * (n + 1) := by exact_mod_cast ht
  congr 1
  · exact mono_ext (by push_cast; linear_combination 84 * ht') (by ring)
  · exact mono_ext (by push_cast; linear_combination 84 * ht') (by ring)

lemma hs_R2₁ : hs R2₁ = ιN h168 MockTheta5.JTP.heckeSumF1 := by
  rw [← hs_hkF₁]
  exact hsum_fubini R2₁ hkF₁ (row R2₁) (fun _ _ => rfl) (fun n => row_R2₁ n)

/-! ## The value of `f_{3,7,3}` at `(x*, y*)` -/

lemma row_T73₁ (k : ℤ) :
    fS hq42' 189 (Z84 ^ (63 : ℤ)) k * mono (189 * k) ((Z84 ^ (21 : ℤ)) ^ k) = hs (row T73₁ k) := by
  unfold fS SK thR
  by_cases hk : 0 ≤ k
  · rw [if_pos hk, show ∀ (A B C : L), A * B * C = (A * C) * B from fun A B C => by ring]
    symm
    refine hs_eq_mul' _ fun s => ?_
    simp only [row_apply, monoFam_apply]
    show t73₁ (k, s) = _
    unfold t73₁
    try dsimp only
    by_cases hs : 0 ≤ s
    · rw [if_pos (show reg _ _ from Or.inl ⟨hk, hs⟩), if_pos hs, mono_mul, mono_mul]
      refine mono_ext (by unfold E73₁ thE; push_cast; ring) ?_
      unfold C73 thC
      rw [if_pos hk]
      simp only [Z_neg']
      zsimp
      exact Z_mod (by omega)
    · rw [if_neg (show ¬ reg k s by unfold reg; omega), if_neg hs, mono_zero_h, mul_zero]
  · rw [if_neg hk, show ∀ (A B C : L), A * -B * C = (-(A * C)) * B from fun A B C => by ring]
    symm
    refine hs_eq_mul' _ fun s => ?_
    simp only [row_apply, monoFam_apply]
    show t73₁ (k, s) = _
    unfold t73₁
    try dsimp only
    by_cases hs : s < 0
    · rw [if_pos (show reg _ _ from Or.inr ⟨by omega, hs⟩), if_pos hs, mono_mul, neg_mono_h, mono_mul]
      refine mono_ext (by unfold E73₁ thE; push_cast; ring) ?_
      unfold C73 thC
      rw [if_neg hk]
      simp only [Z_neg']
      zsimp
      exact Z_mod (by omega)
    · rw [if_neg (show ¬ reg k s by unfold reg; omega), if_neg hs, mono_zero_h, mul_zero]

/-- **HM (8.12) at the MTC₀ point**: `f_{3,7,3}(x*, y*, q) = (q;q)_∞ f₀(Q)` with `Q = t^{168}`. -/
theorem fS_xstar₁ :
    ev (fS hq42' 189 (Z84 ^ (63 : ℤ))) 189 (Z84 ^ (21 : ℤ)) =
      ιN h168 (MockTheta5.JTP.qfacInf * MockTheta5.JTP.f1) := by
  have hE := fS_ent hq42' 189 (Z84 ^ (63 : ℤ))
  rw [ev_eq hE, MockTheta5.JTP.qfacInf_mul_f1_hecke, ← hs_R2₁, ← hs_T73₁]
  exact (hsum_fubini T73₁ (evFam hE 189 (Z84 ^ (21 : ℤ))) (row T73₁) (fun _ _ => rfl)
    (fun k => by rw [evFam_apply]; exact row_T73₁ k)).symm

end MTC
