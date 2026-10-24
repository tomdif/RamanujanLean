/-
# The Hecke side at the MTC₀ point: `f_{3,7,3}(x*, y*, q) = (q;q)_∞ f₀` (HM (8.12))

With `q = t^{42}`, `x* = Z²¹ t^{105} = i s⁵`, `y* = Z⁶³ t^{105} = −i s⁵` (`s = t^{21}`) and `Q = s⁸ = t^{168}`:

`f_{3,7,3}(x*, y*, q) = Σ_{sg r = sg s} sg(r)(−1)^{r+s} i^{r−s} s^{3r²+14rs+3s²+2r+2s}`.

* the terms with `r − s` odd cancel in pairs under `(r, s) ↦ (s, r)` (`hs_Todd`);
* the terms with `r = n + j, s = n − j` (`n ≥ 0`) and `r = j − n − 1, s = −j − n − 1` are exactly
  Andrews' Hecke sum `Σ_{n≥0} Σ_{|j|≤n} (−1)^j Q^{n(5n+1)/2 − j²}(1 − Q^{4n+2})` (`hs_R2`).

`fS_xstar`: `ev fS (x*) = ιN (q;q)_∞ f₀`, with `ιN : ℤ⟦X⟧ → ℂ((t))`, `X ↦ t^{168}`.
-/
import RamanujanTau.MTC.F373
import RamanujanTau.MTC.Z84
import RamanujanTau.MockTheta5F0Pair
import RamanujanTau.ALJacobi

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset

/-! ## Generic facts -/

lemma hs_eq_mul' {ι : Type*} {s u : SummableFamily ℤ ℂ ι} (a : L) (h : ∀ k, u k = a * s k) :
    hs u = a * hs s := by
  rw [hs, hs, ← SummableFamily.hsum_smul]
  congr 1; ext k : 1
  simp [HahnSeries.of_symm_smul_of_eq_mul, h k]

lemma hs_eq_finset_sum {ι : Type*} {s : SummableFamily ℤ ℂ ι} (S : Finset ι) (h : ∀ i ∉ S, s i = 0) :
    hs s = ∑ i ∈ S, s i := by
  ext g
  rw [hs, SummableFamily.coeff_hsum_eq_sum_of_subset (t := S) (fun i hi => by
    by_contra hS; apply hi; rw [h i hS, HahnSeries.coeff_zero]), HahnSeries.coeff_sum]

lemma eq_zero_of_eq_neg' {x : L} (h : x = -1 * x) : x = 0 := by
  have h2 : x + x = 0 := by linear_combination h
  ext n
  have := congrArg (fun f : L => f.coeff n) h2
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero] at this
  simpa using (add_self_eq_zero.mp this)

lemma neg_mono_h (E : ℤ) (C : ℂ) : -(mono E C : L) = mono E (-C) := by simp [mono]

lemma mono_zero_h (E : ℤ) : (mono E (0 : ℂ) : L) = 0 := by simp [mono]

lemma sum_Icc_sym (f : ℤ → L) (n : ℕ) :
    ∑ j ∈ Finset.Icc (-(n : ℤ)) n, f j = f 0 + ∑ i ∈ Finset.range n, (f ((i : ℤ) + 1) + f (-((i : ℤ) + 1))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show (((n + 1 : ℕ) : ℤ)) = (n : ℤ) + 1 by push_cast; ring,
      show Finset.Icc (-((n : ℤ) + 1)) ((n : ℤ) + 1) =
        insert (-((n : ℤ) + 1)) (insert ((n : ℤ) + 1) (Finset.Icc (-(n : ℤ)) n)) by
        ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega,
      Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega),
      Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), ih, Finset.sum_range_succ]
    ring

/-! ## `ιN` on monomials -/

section IotaN
variable {N : ℕ} (hN : 1 ≤ N)

lemma ιN_X : ιN hN PowerSeries.X = mono N 1 := by
  simp only [ιN, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    PowerSeries.expand_X, map_pow, PowerSeries.map_X]
  rw [HahnSeries.ofPowerSeries_X, mono, single_pow]
  simp
lemma ιN_Xpow (k : ℕ) : ιN hN (PowerSeries.X ^ k) = mono (N * k) 1 := by
  rw [map_pow, ιN_X, mono, single_pow]; simp [mono, mul_comm]
lemma neg_one_L : (-1 : L) = mono 0 (-1) := by rw [mono, single_neg, HahnSeries.single_zero_one]
lemma neg_one_pow_L (m : ℕ) : (-1 : L) ^ m = mono 0 ((-1) ^ m) := by
  rw [neg_one_L]
  show (single 0 (-1) : L) ^ m = single 0 ((-1) ^ m)
  rw [single_pow, smul_zero]
lemma mono_pow1 (E : ℤ) (k : ℕ) : (mono E 1 : L) ^ k = mono (k * E) 1 := by
  show (single E (1 : ℂ) : L) ^ k = single ((k : ℤ) * E) 1
  rw [single_pow, one_pow, nsmul_eq_mul]

lemma ιN_Vth (n : ℕ) :
    ιN hN (MockTheta5.Bailey.Vth n) =
      ∑ j ∈ Finset.Icc (-(n : ℤ)) n, mono (N * ((n : ℤ) ^ 2 - j ^ 2)) ((-1) ^ j) := by
  rw [sum_Icc_sym, MockTheta5.Bailey.Vth_eq_sum, map_add, map_mul, map_sum, ιN_Xpow]
  simp only [map_mul, map_pow, map_neg, map_one, map_ofNat, ιN_X, neg_one_pow_L, mono_pow1, mono_mul]
  refine congrArg₂ (· + ·) (mono_ext (by push_cast; ring) (by norm_num)) ?_
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    have hle : (i + 1) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hc1 : ((-1 : ℂ)) ^ ((i : ℤ) + 1) = (-1) ^ (i + 1) := by
      rw [show ((i : ℤ) + 1) = ((i + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    have hc2 : ((-1 : ℂ)) ^ (-((i : ℤ) + 1)) = (-1) ^ (i + 1) := by
      rw [zpow_neg, hc1, ← inv_pow, inv_neg, inv_one]
    rw [two_mul]
    exact congrArg₂ (· + ·) (mono_ext (by push_cast [Nat.cast_sub hle]; ring) (by rw [hc1]; ring))
      (mono_ext (by push_cast [Nat.cast_sub hle]; ring) (by rw [hc2]; ring))

end IotaN

/-! ## The `(r, s)` family of `f_{3,7,3}(x*, y*)` -/

/-- `sg r = sg s`. -/
def reg (r s : ℤ) : Prop := (0 ≤ r ∧ 0 ≤ s) ∨ (r < 0 ∧ s < 0)

instance (r s : ℤ) : Decidable (reg r s) := by unfold reg; infer_instance

/-- the exponent `42(3C(r,2) + 7rs + 3C(s,2)) + 105(r + s)`. -/
def E73 (r s : ℤ) : ℤ := 42 * (3 * c2 r + 7 * r * s + 3 * c2 s) + 105 * (r + s)

/-- the coefficient `sg(r)(−1)^{r+s} i^r (−i)^s`. -/
noncomputable def C73 (r s : ℤ) : ℂ := (if 0 ≤ r then 1 else -1) * (-1) ^ (r + s) * Z84 ^ (21 * r + 63 * s)

lemma E73_bound {r s : ℤ} (h : reg r s) : 21 * (|r| + |s|) ≤ E73 r s := by
  unfold E73
  have h1 := two_c2 r; have h2 := two_c2 s
  rcases h with ⟨hr, hs⟩ | ⟨hr, hs⟩
  · rw [abs_of_nonneg hr, abs_of_nonneg hs]
    nlinarith [mul_nonneg hr hs, mul_nonneg hr hr, mul_nonneg hs hs]
  · rw [abs_of_neg hr, abs_of_neg hs]
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ -r) (by linarith : (0 : ℤ) ≤ -s),
      mul_nonneg (by linarith : (0 : ℤ) ≤ -r - 1) (by linarith : (0 : ℤ) ≤ -r),
      mul_nonneg (by linarith : (0 : ℤ) ≤ -s - 1) (by linarith : (0 : ℤ) ≤ -s)]

noncomputable def t73 (p : ℤ × ℤ) : L := if reg p.1 p.2 then mono (E73 p.1 p.2) (C73 p.1 p.2) else 0

lemma t73_lb (p : ℤ × ℤ) (n : ℤ) (hn : (t73 p).coeff n ≠ 0) : reg p.1 p.2 ∧ n = E73 p.1 p.2 := by
  unfold t73 at hn
  split_ifs at hn with h
  · exact ⟨h, coeff_mono_ne hn⟩
  · simp at hn

lemma t73_hD (p : ℤ × ℤ) (n : ℤ) (hn : n < 0) : (t73 p).coeff n = 0 := by
  by_contra h
  obtain ⟨hr, rfl⟩ := t73_lb p n h
  have := E73_bound hr; have := abs_nonneg p.1; have := abs_nonneg p.2; omega

lemma box_fin (n : ℤ) (P : ℤ × ℤ → Prop) (h : ∀ p, P p → 21 * (|p.1| + |p.2|) ≤ n) : {p | P p}.Finite :=
  ((Finset.Icc (-n) n ×ˢ Finset.Icc (-n) n : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)).toFinite.subset fun p hp => by
    have := h p hp
    have a1 := le_abs_self p.1; have a2 := neg_abs_le p.1; have a3 := le_abs_self p.2
    have a4 := neg_abs_le p.2
    simp only [Finset.coe_product, Set.mem_prod, Finset.coe_Icc, Set.mem_Icc]
    omega

noncomputable def T73 : SummableFamily ℤ ℂ (ℤ × ℤ) :=
  ofSupp t73 0 (fun p n hn => t73_hD p n hn)
    (fun n => box_fin n _ fun p hp => by obtain ⟨hr, rfl⟩ := t73_lb p n hp; exact E73_bound hr)

/-! ## The odd part cancels -/

noncomputable def todd (p : ℤ × ℤ) : L := if (p.1 - p.2) % 2 = 1 then t73 p else 0

noncomputable def Todd : SummableFamily ℤ ℂ (ℤ × ℤ) :=
  ofSupp todd 0 (fun p n hn => by
    unfold todd
    split_ifs with h
    · exact t73_hD p n hn
    · simp)
    (fun n => box_fin n _ fun p hp => by
      unfold todd at hp
      split_ifs at hp
      · obtain ⟨hr, rfl⟩ := t73_lb p n hp; exact E73_bound hr
      · simp at hp)

lemma C73_swap {r s : ℤ} (ho : (r - s) % 2 = 1) (hr : reg r s) : C73 s r = -C73 r s := by
  unfold C73
  have hsign : (if 0 ≤ s then (1 : ℂ) else -1) = (if 0 ≤ r then 1 else -1) := by
    unfold reg at hr; split_ifs <;> first | rfl | (exfalso; omega)
  rw [hsign]
  by_cases h0 : 0 ≤ r
  · simp only [if_pos h0]
    simp only [Z_neg']
    zsimp
    exact Z_mod (by omega)
  · simp only [if_neg h0]
    simp only [Z_neg']
    zsimp
    exact Z_mod (by omega)

lemma todd_swap (p : ℤ × ℤ) : todd (p.2, p.1) = -1 * todd p := by
  obtain ⟨r, s⟩ := p
  unfold todd t73
  try dsimp only
  by_cases ho : (r - s) % 2 = 1
  · have ho' : (s - r) % 2 = 1 := by omega
    rw [if_pos ho', if_pos ho]
    by_cases hr : reg r s
    · have hr' : reg s r := by unfold reg at hr ⊢; omega
      rw [if_pos hr', if_pos hr, mono_ext (show E73 s r = E73 r s by unfold E73; ring) (C73_swap ho hr),
        ← neg_mono_h]
      ring
    · have hr' : ¬ reg s r := by unfold reg at hr ⊢; omega
      rw [if_neg hr', if_neg hr, mul_zero]
  · have ho' : ¬ (s - r) % 2 = 1 := by omega
    rw [if_neg ho', if_neg ho, mul_zero]

lemma hs_Todd : hs Todd = 0 :=
  eq_zero_of_eq_neg' (hsum_reindex Todd Todd (Equiv.prodComm ℤ ℤ) (-1) fun p => todd_swap p)

/-! ## The even part is Andrews' Hecke sum -/

noncomputable def r2 (q : ℕ × (ℤ × Fin 2)) : L :=
  if |q.2.1| ≤ (q.1 : ℤ) then
    (if q.2.2 = 0 then mono (84 * (5 * (q.1 : ℤ) ^ 2 + q.1) - 168 * q.2.1 ^ 2) ((-1) ^ q.2.1)
     else mono (84 * (5 * (q.1 : ℤ) ^ 2 + 9 * q.1 + 4) - 168 * q.2.1 ^ 2) (-(-1) ^ q.2.1))
  else 0

lemma r2_lb (q : ℕ × (ℤ × Fin 2)) (n : ℤ) (hn : (r2 q).coeff n ≠ 0) :
    84 * (q.1 : ℤ) ≤ n ∧ |q.2.1| ≤ (q.1 : ℤ) := by
  unfold r2 at hn
  split_ifs at hn with h1 h2
  · have := coeff_mono_ne hn
    have hj : q.2.1 ^ 2 ≤ (q.1 : ℤ) ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    exact ⟨by nlinarith [sq_nonneg (q.1 : ℤ)], h1⟩
  · have := coeff_mono_ne hn
    have hj : q.2.1 ^ 2 ≤ (q.1 : ℤ) ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    exact ⟨by nlinarith [sq_nonneg (q.1 : ℤ)], h1⟩
  · simp at hn

noncomputable def R2 : SummableFamily ℤ ℂ (ℕ × (ℤ × Fin 2)) :=
  ofSupp r2 0 (fun q n hn => by
      by_contra h
      have := (r2_lb q n h).1
      have : (0 : ℤ) ≤ q.1 := by positivity
      omega)
    (fun n => ((Finset.range (n.toNat + 1) ×ˢ (Finset.Icc (-n) n ×ˢ Finset.univ) :
        Finset (ℕ × (ℤ × Fin 2))) : Set _).toFinite.subset fun q hq => by
      obtain ⟨h1, h2⟩ := r2_lb q n hq
      have a1 := le_abs_self q.2.1; have a2 := neg_abs_le q.2.1
      simp only [Finset.coe_product, Set.mem_prod, Finset.coe_range, Set.mem_Iio, Finset.coe_Icc,
        Set.mem_Icc, Finset.coe_univ, Set.mem_univ, and_true]
      omega)

/-- the embedding `(n, j, 0) ↦ (n + j, n − j)`, `(n, j, 1) ↦ (j − n − 1, −j − n − 1)`. -/
def psi (q : ℕ × (ℤ × Fin 2)) : ℤ × ℤ :=
  if q.2.2 = 0 then ((q.1 : ℤ) + q.2.1, (q.1 : ℤ) - q.2.1) else (q.2.1 - q.1 - 1, -q.2.1 - q.1 - 1)

lemma psi_diff (q : ℕ × (ℤ × Fin 2)) : (psi q).1 - (psi q).2 = 2 * q.2.1 := by
  unfold psi; split_ifs <;> simp only <;> ring

lemma psi_inj : Function.Injective psi := by
  rintro ⟨n, j, p⟩ ⟨n', j', p'⟩ h
  fin_cases p <;> fin_cases p' <;> simp [psi, Prod.ext_iff] at h ⊢ <;> omega

def psiE : ℕ × (ℤ × Fin 2) ↪ ℤ × ℤ := ⟨psi, psi_inj⟩

lemma t73_psi (q : ℕ × (ℤ × Fin 2)) : t73 (psi q) = r2 q := by
  obtain ⟨n, j, p⟩ := q
  have h1 := two_c2 ((n : ℤ) + j); have h2 := two_c2 ((n : ℤ) - j)
  have h3 := two_c2 (j - n - 1); have h4 := two_c2 (-j - n - 1)
  fin_cases p
  · show (if reg ((n : ℤ) + j) ((n : ℤ) - j) then mono (E73 ((n : ℤ) + j) ((n : ℤ) - j))
        (C73 ((n : ℤ) + j) ((n : ℤ) - j)) else 0) =
      (if |j| ≤ (n : ℤ) then mono (84 * (5 * (n : ℤ) ^ 2 + n) - 168 * j ^ 2) ((-1) ^ j) else 0)
    by_cases hj : |j| ≤ (n : ℤ)
    · have := abs_le.mp hj
      rw [if_pos (show reg _ _ from Or.inl ⟨by omega, by omega⟩), if_pos hj]
      refine mono_ext (by unfold E73; linear_combination 63 * h1 + 63 * h2) ?_
      unfold C73
      rw [if_pos (show (0 : ℤ) ≤ (n : ℤ) + j by omega)]
      simp only [Z_neg']
      zsimp
      exact Z_mod (by omega)
    · rw [if_neg (show ¬ reg ((n : ℤ) + j) ((n : ℤ) - j) by unfold reg; intro h; apply hj; rw [abs_le]; omega), if_neg hj]
  · show (if reg (j - n - 1) (-j - n - 1) then mono (E73 (j - n - 1) (-j - n - 1))
        (C73 (j - n - 1) (-j - n - 1)) else 0) =
      (if |j| ≤ (n : ℤ) then mono (84 * (5 * (n : ℤ) ^ 2 + 9 * n + 4) - 168 * j ^ 2) (-(-1) ^ j) else 0)
    by_cases hj : |j| ≤ (n : ℤ)
    · have := abs_le.mp hj
      rw [if_pos (show reg _ _ from Or.inr ⟨by omega, by omega⟩), if_pos hj]
      refine mono_ext (by unfold E73; linear_combination 63 * h3 + 63 * h4) ?_
      unfold C73
      rw [if_neg (show ¬ (0 : ℤ) ≤ j - n - 1 by omega)]
      simp only [Z_neg']
      zsimp
      exact Z_mod (by omega)
    · rw [if_neg (show ¬ reg (j - n - 1) (-j - n - 1) by unfold reg; intro h; apply hj; rw [abs_le]; omega), if_neg hj]

lemma todd_psi (q : ℕ × (ℤ × Fin 2)) : todd (psi q) = 0 := by
  unfold todd
  rw [if_neg (show ¬ ((psi q).1 - (psi q).2) % 2 = 1 by rw [psi_diff]; omega)]

lemma T73_split : T73 = R2.embDomain psiE + Todd := by
  ext ⟨r, s⟩ : 1
  rw [SummableFamily.add_apply]
  show t73 (r, s) = _ + todd (r, s)
  by_cases ho : (r - s) % 2 = 1
  · rw [SummableFamily.embDomain_notin_range (s := R2) (f := psiE) (b := (r, s)) (by
      rintro ⟨q, hq⟩
      have := psi_diff q
      rw [show psi q = (r, s) from hq] at this
      simp only at this; omega)]
    unfold todd
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
    show t73 (psi q) = r2 q + todd (psi q)
    rw [t73_psi, todd_psi, add_zero]

lemma hs_T73 : hs T73 = hs R2 := by
  rw [T73_split, hs_eq, SummableFamily.hsum_add, SummableFamily.hsum_embDomain, ← hs_eq, ← hs_eq, hs_Todd,
    add_zero]

/-! ## Rows of `R2` and the Hecke sum -/

lemma h168 : 1 ≤ 168 := by norm_num

lemma heckeF0_coeff_lt (n k : ℕ) (hk : k < n) : PowerSeries.coeff k (MockTheta5.Bailey.heckeF0 n) = 0 := by
  unfold MockTheta5.Bailey.heckeF0
  rw [mul_assoc, PowerSeries.coeff_X_pow_mul', if_neg]
  have : n ≤ n ^ 2 := Nat.le_self_pow two_ne_zero n
  omega

noncomputable def hkF : SummableFamily ℤ ℂ ℕ :=
  ofSupp (fun n => ιN h168 (MockTheta5.Bailey.heckeF0 n)) 0 (fun n m hm => ιN_coeff_neg h168 _ hm)
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
          rw [heckeF0_coeff_lt n (k / 168) (by have := Nat.div_le_self k 168; omega)]
          simp
        · simp at hn)

lemma hs_hkF : hs hkF = ιN h168 MockTheta5.JTP.heckeSumF0 := by
  ext m
  rw [hs, SummableFamily.coeff_hsum]
  rcases lt_or_ge m 0 with hm | hm
  · rw [ιN_coeff_neg h168 _ hm]
    exact finsum_eq_zero_of_forall_eq_zero fun n => ιN_coeff_neg h168 _ hm
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = k := ⟨m.toNat, by omega⟩
    simp only [hkF, ofSupp_apply, ιN_coeff_nat]
    split_ifs with hd
    · rw [MockTheta5.JTP.heckeSumF0, PowerSeries.coeff_mk, map_sum, Int.cast_sum,
        finsum_eq_sum_of_support_subset (s := Finset.range (k / 168 + 1))]
      intro n hn
      rw [Function.mem_support] at hn
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra hlt
      apply hn
      rw [heckeF0_coeff_lt n (k / 168) (by omega)]
      simp
    · simp

lemma two_triF (n : ℕ) : 2 * MockTheta5.Bailey.triF n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [MockTheta5.Bailey.triF_succ]; nlinarith

lemma row_R2 (n : ℕ) : ιN h168 (MockTheta5.Bailey.heckeF0 n) = hs (row R2 n) := by
  rw [hs_eq_finset_sum (Finset.Icc (-(n : ℤ)) n ×ˢ Finset.univ) (fun jp hjp => by
    simp only [row_apply]
    show r2 (n, jp) = 0
    unfold r2
    rw [if_neg]
    intro h
    apply hjp
    simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_univ, and_true]
    exact abs_le.mp h)]
  rw [Finset.sum_product]
  simp only [row_apply, Fin.sum_univ_two]
  unfold MockTheta5.Bailey.heckeF0
  rw [map_mul, map_mul, ιN_Vth h168, map_sub, map_one, ιN_Xpow, ιN_Xpow, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : |j| ≤ (n : ℤ) := abs_le.mpr (Finset.mem_Icc.mp hj)
  show _ = r2 (n, j, 0) + r2 (n, j, 1)
  rw [show r2 (n, j, 0) = mono (84 * (5 * (n : ℤ) ^ 2 + n) - 168 * j ^ 2) ((-1) ^ j) from by
      show (if |j| ≤ (n : ℤ) then (if (0 : Fin 2) = 0 then _ else _) else 0) = _
      rw [if_pos hjn]; rfl,
    show r2 (n, j, 1) = mono (84 * (5 * (n : ℤ) ^ 2 + 9 * n + 4) - 168 * j ^ 2) (-(-1) ^ j) from by
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

lemma hs_R2 : hs R2 = ιN h168 MockTheta5.JTP.heckeSumF0 := by
  rw [← hs_hkF]
  exact hsum_fubini R2 hkF (row R2) (fun _ _ => rfl) (fun n => row_R2 n)

/-! ## The value of `f_{3,7,3}` at `(x*, y*)` -/

lemma hq42' : 1 ≤ 42 := by norm_num

lemma row_T73 (k : ℤ) :
    fS hq42' 105 (Z84 ^ (63 : ℤ)) k * mono (105 * k) ((Z84 ^ (21 : ℤ)) ^ k) = hs (row T73 k) := by
  unfold fS SK thR
  by_cases hk : 0 ≤ k
  · rw [if_pos hk, show ∀ (A B C : L), A * B * C = (A * C) * B from fun A B C => by ring]
    symm
    refine hs_eq_mul' _ fun s => ?_
    simp only [row_apply, monoFam_apply]
    show t73 (k, s) = _
    unfold t73
    try dsimp only
    by_cases hs : 0 ≤ s
    · rw [if_pos (show reg _ _ from Or.inl ⟨hk, hs⟩), if_pos hs, mono_mul, mono_mul]
      refine mono_ext (by unfold E73 thE; push_cast; ring) ?_
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
    show t73 (k, s) = _
    unfold t73
    try dsimp only
    by_cases hs : s < 0
    · rw [if_pos (show reg _ _ from Or.inr ⟨by omega, hs⟩), if_pos hs, mono_mul, neg_mono_h, mono_mul]
      refine mono_ext (by unfold E73 thE; push_cast; ring) ?_
      unfold C73 thC
      rw [if_neg hk]
      simp only [Z_neg']
      zsimp
      exact Z_mod (by omega)
    · rw [if_neg (show ¬ reg k s by unfold reg; omega), if_neg hs, mono_zero_h, mul_zero]

/-- **HM (8.12) at the MTC₀ point**: `f_{3,7,3}(x*, y*, q) = (q;q)_∞ f₀(Q)` with `Q = t^{168}`. -/
theorem fS_xstar :
    ev (fS hq42' 105 (Z84 ^ (63 : ℤ))) 105 (Z84 ^ (21 : ℤ)) =
      ιN h168 (MockTheta5.JTP.qfacInf * MockTheta5.JTP.f0) := by
  have hE := fS_ent hq42' 105 (Z84 ^ (63 : ℤ))
  rw [ev_eq hE, MockTheta5.JTP.qfacInf_mul_f0_hecke, ← hs_R2, ← hs_T73]
  exact (hsum_fubini T73 (evFam hE 105 (Z84 ^ (21 : ℤ))) (row T73) (fun _ _ => rfl)
    (fun k => by rw [evFam_apply]; exact row_T73 k)).symm

end MTC
