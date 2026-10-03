/-
# Appell–Lerch sums at boundary points

Extends `ALChangeZ` to points where `val(xp)` is anywhere in `(−N, N)` (including `0`, i.e. `xp` a
constant `≠ 1`, e.g. a root of unity). The `r = 1` slice of the Appell sum is treated through the exact
quotient `θ(y)/(1−y) = Σ_k y^k Θ(k)`, `Θ(k) = Σ_{i ≤ k} (−1)^i q^{C(i,2)}`, which decays on both sides.
-/
import RamanujanTau.ALChangeZ

set_option autoImplicit false

namespace ALz
open HahnSeries Finset

section PartialTheta
variable {N : ℕ} (hN : 1 ≤ N)
include hN

/-- `Σ_{i : P i} (−1)^i q^{C(i,2)}`. -/
noncomputable def thInd (P : ℤ → Prop) [DecidablePred P] : SummableFamily ℤ ℂ ℤ :=
  monoFam (thE N 0) (fun i => if P i then (-1) ^ i else 0) _ (thE_lb hN 0) (thE_fin hN 0)

/-- the partial theta sum `Θ(k) = Σ_{i ≤ k} (−1)^i q^{C(i,2)}`. -/
noncomputable def Θlo (k : ℤ) : L := hs (thInd hN (· ≤ k))

lemma thInd_add (P : ℤ → Prop) [DecidablePred P] :
    hs (thInd hN P) + hs (thInd hN (fun i => ¬ P i)) = 0 := by
  have h := θ_one hN
  rw [θ] at h
  rw [hs_eq, hs_eq, ← SummableFamily.hsum_add, ← hs_eq, ← h]
  refine hsum_congr _ _ fun i => ?_
  simp only [SummableFamily.add_apply, thInd, thF, monoFam_apply, thC, one_zpow, mul_one]
  split_ifs <;> simp [mono]

/-- the upper form: `Θ(k) = −Σ_{i > k} (−1)^i q^{C(i,2)}`. -/
lemma Θlo_upper (k : ℤ) : Θlo hN k = -hs (thInd hN (fun i => ¬ i ≤ k)) := by
  have := thInd_add hN (· ≤ k)
  rw [Θlo]; linear_combination this

lemma thInd_coeff_zero (P : ℤ → Prop) [DecidablePred P] (n : ℤ) (h : ∀ i, P i → n < thE N 0 i) :
    (hs (thInd hN P)).coeff n = 0 := by
  rw [thInd, monoFam_coeff]
  refine finsum_eq_zero_of_forall_eq_zero fun i => ?_
  split_ifs with h1 h2
  · exact absurd h1 (h i h2).ne'
  · rfl
  · rfl

/-- `Θ(k) − Θ(k−1) = (−1)^k q^{C(k,2)}`. -/
lemma Θlo_sub (k : ℤ) : Θlo hN k - Θlo hN (k - 1) = mono (N * c2 k) ((-1) ^ k) := by
  rw [Θlo, Θlo, hs_eq, hs_eq, ← SummableFamily.hsum_sub]
  have : (thInd hN (· ≤ k) - thInd hN (· ≤ k - 1)) = SummableFamily.single k (mono (N * c2 k) ((-1) ^ k)) := by
    refine SummableFamily.coe_injective (funext fun i => ?_)
    simp only [SummableFamily.sub_apply, thInd, monoFam_apply, thE]
    change _ = (Pi.single k (mono (N * c2 k) ((-1) ^ k)) : ℤ → L) i
    by_cases hi : i = k
    · subst hi; simp
    · rw [Pi.single_apply, if_neg hi]
      by_cases h2 : i ≤ k - 1
      · rw [if_pos (by omega), if_pos h2, sub_self]
      · rw [if_neg (by omega), if_neg h2, sub_self]
  rw [this, SummableFamily.hsum_single]

/-- valuation bound: `Θ(k)` vanishes below `N·min(C(k,2), C(k+1,2))`. -/
lemma Θlo_coeff_zero (k n : ℤ) (h : n < N * c2 k ∧ n < N * c2 (k + 1)) : (Θlo hN k).coeff n = 0 := by
  have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
  rcases lt_or_ge k 0 with hk | hk
  · rw [Θlo]
    refine thInd_coeff_zero hN _ n fun i hi => ?_
    simp only [thE, zero_mul, add_zero]
    have h1 := two_c2 i; have h2 := two_c2 k
    have : c2 k ≤ c2 i := by nlinarith
    nlinarith
  · rw [Θlo_upper, coeff_neg, thInd_coeff_zero hN _ n fun i hi => ?_, neg_zero]
    simp only [thE, zero_mul, add_zero]
    have h1 := two_c2 i; have h2 := two_c2 (k + 1)
    have : c2 (k + 1) ≤ c2 i := by push Not at hi; nlinarith
    nlinarith

end PartialTheta


section Squot
variable {N : ℕ} (hN : 1 ≤ N)
include hN

omit hN in
lemma coeff_mono_mul (e n : ℤ) (c : ℂ) (X : L) : (mono e c * X).coeff n = c * X.coeff (n - e) := by
  have := coeff_single_mul_add (r := c) (x := X) (a := n - e) (b := e)
  rw [show n - e + e = n by ring] at this
  exact this

lemma squot_lb (e k n : ℤ) (h : ((mono (e * k) (1 : ℂ)) * Θlo hN k).coeff n ≠ 0) :
    thE N e k ≤ n ∨ thE N e (k + 1) ≤ n + e := by
  rw [coeff_mono_mul, one_mul] at h
  by_contra hc
  push Not at hc
  apply h
  refine Θlo_coeff_zero hN k _ ⟨?_, ?_⟩ <;> unfold thE at hc
  · linarith [hc.1]
  · have := hc.2; rw [c2_succ] at this ⊢; nlinarith [hc.2]

/-- the family `k ↦ y^k Θ(k)`, `y = c tᵉ`. -/
noncomputable def sqF (e : ℤ) (c : ℂ) : SummableFamily ℤ ℂ ℤ :=
  ofSupp (fun k => mono (e * k) (c ^ k) * Θlo hN k) (-(e * e) - 1 - |e|)
    (fun k n hn => by
      rw [coeff_mono_mul]
      have h2 := thE_lb hN e k
      have h3 := thE_lb hN e (k + 1)
      by_cases hc : (Θlo hN k).coeff (n - e * k) = 0
      · rw [hc, mul_zero]
      · exfalso
        have h4 := le_abs_self e
        have h5 := neg_abs_le e
        rcases squot_lb hN e k n (by rw [coeff_mono_mul, one_mul]; exact hc) with h' | h' <;> linarith)
    (fun n => by
      refine (((Set.finite_Icc (-(2 * |n| + 2 * |e| + 1)) (2 * |n| + 2 * |e| + 1)).union
        (Set.finite_Icc (-(2 * |n + e| + 2 * |e| + 1) - 1) (2 * |n + e| + 2 * |e| + 1)))).subset fun k hk => ?_
      simp only [Set.mem_setOf_eq] at hk
      rw [coeff_mono_mul] at hk
      have hc : (Θlo hN k).coeff (n - e * k) ≠ 0 := right_ne_zero_of_mul hk
      rcases squot_lb hN e k n (by rw [coeff_mono_mul, one_mul]; exact hc) with h | h
      · left; have := thE_le_bound hN e k n h; rw [abs_le] at this; exact ⟨this.1, this.2⟩
      · right; have := thE_le_bound hN e (k + 1) (n + e) h; rw [abs_le] at this
        exact ⟨by linarith [this.1], by linarith [this.2]⟩)

lemma sqF_apply (e : ℤ) (c : ℂ) (k : ℤ) : sqF hN e c k = mono (e * k) (c ^ k) * Θlo hN k := rfl

/-- `(1 − y) · Σ_k y^k Θ(k) = θ(y)`. -/
theorem sq_eval (e : ℤ) {c : ℂ} (hc : c ≠ 0) : (1 - mono e c) * hs (sqF hN e c) = θ hN e c := by
  have hy : mono e c * hs (sqF hN e c) =
      hs (SummableFamily.Equiv (Equiv.addRight 1) (mono e c • sqF hN e c)) := by
    rw [hs_eq, hs_eq, SummableFamily.hsum_equiv, SummableFamily.hsum_smul]
  rw [sub_mul, one_mul, hy, hs_eq, hs_eq, ← SummableFamily.hsum_sub, ← hs_eq, θ]
  refine hsum_congr _ _ fun k => ?_
  simp only [SummableFamily.sub_apply, SummableFamily.Equiv_toFun,
    Equiv.addRight_symm_apply, SummableFamily.smul_apply, HahnSeries.of_symm_smul_of_eq_mul, sqF_apply]
  rw [show (k + -1 : ℤ) = k - 1 by ring, ← mul_assoc, mono_mul,
    show e + e * (k - 1) = e * k by ring, ← zpow_one_add₀ hc, show 1 + (k - 1) = k by ring, ← mul_sub,
    Θlo_sub, mono_mul, thF_apply, thT]
  congr 1
  · unfold thE; ring
  · unfold thC; ring

end Squot


/-! ## Splitting off the `r = 1` slice of `𝒜_k` -/

section Split1
variable {N : ℕ} (hN : 1 ≤ N)
include hN

/-- `𝒜_k` without its `r = 1` slice. -/
noncomputable def aaF1 (a : ℤ) (cx : ℂ) (k : ℤ) : SummableFamily ℤ ℂ (ℤ × ℤ) :=
  monoFam (aaE N a k) (fun rj => if rj.1 = 1 then 0 else aaC cx k rj) _ (aaE_lb hN a k) (aaE_fin hN a k)

def slice1 : ℤ ↪ ℤ × ℤ := ⟨fun j => (1, j), fun _ _ h => (Prod.mk.inj h).2⟩

/-- the `r = 1` slice is `−x^{k−1} Θ(k−1)`. -/
lemma hs_row1 (a : ℤ) (cx : ℂ) (k : ℤ) :
    hs (row (aaF hN a cx k) 1) = -mono (a * (k - 1)) (cx ^ (k - 1)) * Θlo hN (k - 1) := by
  refine hsum_reindex (thInd hN (· ≤ k - 1)) _ (Equiv.subLeft (k - 1)) _ fun i => ?_
  rw [row_apply, aaF_apply, Equiv.subLeft_apply, thInd, monoFam_apply]
  simp only
  by_cases hi : i ≤ k - 1
  · have hc : cone 1 (k - 1 - i) := Or.inl ⟨le_rfl, by omega⟩
    rw [if_pos hc, if_pos hi]
    rw [show -mono (a * (k - 1)) (cx ^ (k - 1)) * mono (thE N 0 i) ((-1) ^ i)
        = mono (a * (k - 1) + thE N 0 i) (-(cx ^ (k - 1) * (-1) ^ i)) by
      have h1 := mono_mul (a * (k - 1)) (thE N 0 i) (cx ^ (k - 1)) ((-1) ^ i)
      rw [show mono (a * (k - 1) + thE N 0 i) (-(cx ^ (k - 1) * (-1) ^ i))
          = -mono (a * (k - 1) + thE N 0 i) (cx ^ (k - 1) * (-1) ^ i) from single_neg _ _, ← h1]
      ring]
    congr 1
    · unfold aaExp thE; rw [show k - 1 - (k - 1 - i) = i by ring]; simp [c2]; ring
    · unfold sgnC; rw [if_pos le_rfl, show (1 : ℤ) + (k - 1 - (k - 1 - i)) = i + 1 by ring,
        zpow_add₀ (by norm_num), show k - 1 = k - 1 from rfl]; ring
  · have hc : ¬ cone 1 (k - 1 - i) := by unfold cone; omega
    rw [if_neg hc, if_neg hi]; simp [mono]

lemma AA_split (a : ℤ) (cx : ℂ) (k : ℤ) :
    AA hN a cx k = hs (aaF1 hN a cx k) - mono (a * (k - 1)) (cx ^ (k - 1)) * Θlo hN (k - 1) := by
  have h : ∀ rj, aaF hN a cx k rj = (aaF1 hN a cx k + (row (aaF hN a cx k) 1).embDomain slice1) rj := by
    rintro ⟨r, j⟩
    simp only [SummableFamily.add_apply, aaF, aaF1, monoFam_apply]
    by_cases hr : r = 1
    · subst hr
      have he : ((row (aaF hN a cx k) 1).embDomain slice1) (slice1 j) = row (aaF hN a cx k) 1 j :=
        SummableFamily.embDomain_image _ _
      change _ = _ + ((row (aaF hN a cx k) 1).embDomain slice1) (slice1 j)
      rw [he]
      simp [mono, aaF]
    · rw [SummableFamily.embDomain_notin_range, if_neg hr, add_zero]
      rintro ⟨j', hj'⟩; exact hr (congrArg Prod.fst hj').symm
  rw [AA, hsum_congr _ _ h, hs_eq, SummableFamily.hsum_add, SummableFamily.hsum_embDomain, ← hs_eq,
    ← hs_eq, hs_row1]
  ring

end Split1


/-! ## The `r ≠ 1` part of `A(x,p)` for `−N < val(xp) < N` -/

section Aser2
variable {N : ℕ}

/-- the cone without its `r = 1` slice. -/
def cone2 (r j : ℤ) : Prop := cone r j ∧ r ≠ 1

instance (r j : ℤ) : Decidable (cone2 r j) := by unfold cone2; infer_instance

lemma cone2_lin {a β r j : ℤ} (hlo : -N < a + β) (hhi : a + β < N) (h : cone2 r j) :
    |j| ≤ (N * (r - 1) + a + β) * j := by
  have hN0 : (0 : ℤ) ≤ N := by positivity
  obtain ⟨h, hr⟩ := h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg h2]
    have : (N : ℤ) ≤ N * (r - 1) := by
      have : (1 : ℤ) ≤ r - 1 := by omega
      nlinarith
    have : 0 ≤ (N * (r - 1) + a + β - 1) * j := mul_nonneg (by omega) h2
    nlinarith
  · rw [abs_of_neg (by omega)]
    have : (N : ℤ) * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hN0 h1
    have : 0 ≤ (N * (r - 1) + a + β + 1) * j :=
      mul_nonneg_of_nonpos_of_nonpos (by nlinarith) (by omega)
    nlinarith

lemma asExp_ge2 (hN : 1 ≤ N) {a β r j : ℤ} (hlo : -N < a + β) (hhi : a + β < N) (h : cone2 r j) :
    c2 r - |β| * |r| + |j| ≤ asExp N a β r j := by
  unfold asExp
  have := cone2_lin hlo hhi h
  have h0 := c2_nonneg r
  have : c2 r ≤ (N : ℤ) * c2 r := le_mul_of_one_le_left h0 (by exact_mod_cast hN)
  have : -(|β| * |r|) ≤ β * r := by rw [← abs_mul]; exact neg_abs_le _
  linarith

variable (N)

def asE2 (a β : ℤ) (rj : ℤ × ℤ) : ℤ := if cone2 rj.1 rj.2 then asExp N a β rj.1 rj.2 else |rj.1| + |rj.2|

noncomputable def asC2 (cx cp : ℂ) (rj : ℤ × ℤ) : ℂ :=
  if cone2 rj.1 rj.2 then sgnC rj.1 * (-1) ^ rj.1 * cp ^ rj.1 * (cx * cp) ^ rj.2 else 0

variable {N}

lemma asE2_lb (hN : 1 ≤ N) {a β : ℤ} (hlo : -N < a + β) (hhi : a + β < N) (rj : ℤ × ℤ) :
    -((|β| + 1) * (|β| + 1)) ≤ asE2 N a β rj := by
  unfold asE2
  split_ifs with hc
  · have := asExp_ge2 hN hlo hhi hc; have := c2_sub_bound β rj.1; have := abs_nonneg rj.2; linarith
  · have := abs_nonneg rj.1; have := abs_nonneg rj.2; nlinarith

lemma asE2_fin (hN : 1 ≤ N) {a β : ℤ} (hlo : -N < a + β) (hhi : a + β < N) (n : ℤ) :
    {rj : ℤ × ℤ | asE2 N a β rj = n}.Finite := by
  set B := 2 * |β| + 1 + 2 * |n + (|β| + 1) * (|β| + 1)| + |n| + (|β| + 1) * (|β| + 1) + |n|
  refine ((Set.finite_Icc (-B) B).prod (Set.finite_Icc (-B) B)).subset fun ⟨r, j⟩ h => ?_
  simp only [Set.mem_setOf_eq, asE2] at h
  have hb := abs_nonneg β; have hn := abs_nonneg n
  have hP : 0 ≤ (|β| + 1) * (|β| + 1) := by positivity
  split_ifs at h with hc
  · have h1 := asExp_ge2 hN hlo hhi hc
    have h2 := c2_sub_bound β r
    have hj : |j| ≤ n + (|β| + 1) * (|β| + 1) := by linarith
    have hr : |r| ≤ 2 * |β| + 1 + 2 * |n + (|β| + 1) * (|β| + 1)| :=
      c2_sub_le β r _ (by have := abs_nonneg j; linarith)
    have := abs_nonneg (n + (|β| + 1) * (|β| + 1))
    simp only [Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> [have := neg_abs_le r; have := le_abs_self r;
      have := neg_abs_le j; have := le_abs_self j] <;> nlinarith [le_abs_self n]
  · have hr := abs_nonneg r; have hj := abs_nonneg j
    have h1 : |r| ≤ |n| := by rw [← h]; have := le_abs_self (|r| + |j|); linarith
    have h2 : |j| ≤ |n| := by rw [← h]; have := le_abs_self (|r| + |j|); linarith
    have := abs_nonneg (n + (|β| + 1) * (|β| + 1))
    simp only [Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> [have := neg_abs_le r; have := le_abs_self r;
      have := neg_abs_le j; have := le_abs_self j] <;> nlinarith

noncomputable def asF2 (hN : 1 ≤ N) {a β : ℤ} (hlo : -N < a + β) (hhi : a + β < N) (cx cp : ℂ) :
    SummableFamily ℤ ℂ (ℤ × ℤ) :=
  monoFam (asE2 N a β) (asC2 cx cp) _ (asE2_lb hN hlo hhi) (asE2_fin hN hlo hhi)

/-- the `r ≠ 1` part of the Appell–Lerch sum. -/
noncomputable def Aser2 (hN : 1 ≤ N) {a β : ℤ} (hlo : -N < a + β) (hhi : a + β < N) (cx cp : ℂ) : L :=
  hs (asF2 hN hlo hhi cx cp)

/-- **the Appell–Lerch sum at a general point** `A(x,p) = A_{r≠1}(x,p) − p/(1 − xp)`. -/
noncomputable def Ab (hN : 1 ≤ N) {a β : ℤ} (hlo : -N < a + β) (hhi : a + β < N) (cx cp : ℂ) : L :=
  Aser2 hN hlo hhi cx cp - mono β cp * (1 - mono (a + β) (cx * cp))⁻¹

end Aser2


section ExtEval
variable {N : ℕ} (hN : 1 ≤ N)
include hN

lemma asF2_apply {a β : ℤ} (hlo : -N < a + β) (hhi : a + β < N) (cx cp : ℂ) (rj : ℤ × ℤ) :
    asF2 hN hlo hhi cx cp rj = if cone2 rj.1 rj.2 then
      mono (asExp N a β rj.1 rj.2) (sgnC rj.1 * (-1) ^ rj.1 * cp ^ rj.1 * (cx * cp) ^ rj.2) else 0 := by
  rw [asF2, monoFam_apply, asE2, asC2]
  split_ifs <;> simp [mono]

lemma aaF1_apply (a : ℤ) (cx : ℂ) (k : ℤ) (rj : ℤ × ℤ) :
    aaF1 hN a cx k rj = if rj.1 = 1 then 0 else aaF hN a cx k rj := by
  rw [aaF1, monoFam_apply, aaF, monoFam_apply]
  split_ifs <;> simp [mono]

lemma aa_eval_pt2 {a β : ℤ} (hlo : -N < a + β) (hhi : a + β < N) {cx cp : ℂ} (hx : cx ≠ 0)
    (hp : cp ≠ 0) (k r j : ℤ) :
    thT N (a + β) (cx * cp) (k - r - j) * asF2 hN hlo hhi cx cp (r, j) =
      (mono β cp) ^ k * aaF1 hN a cx k (r, j) := by
  rw [asF2_apply, aaF1_apply]
  simp only
  by_cases hr : r = 1
  · have : ¬ cone2 r j := fun h => h.2 hr
    rw [if_neg this, if_pos hr, mul_zero, mul_zero]
  · rw [if_neg hr]
    by_cases hc : cone r j
    · have h2 : cone2 r j := ⟨hc, hr⟩
      rw [if_pos h2]
      have hlo' : True := trivial
      rw [aaF_apply, if_pos hc, thT, mono_mul, mono_zpow, mono_mul]
      congr 1
      · unfold thE asExp aaExp; ring
      · unfold thC
        have e1 : (cx * cp) ^ (k - r - j) * (cx * cp) ^ j = cx ^ (k - r) * cp ^ (k - r) := by
          rw [← zpow_add₀ (mul_ne_zero hx hp), mul_zpow]; ring_nf
        have e2 : cp ^ k = cp ^ r * cp ^ (k - r) := by rw [← zpow_add₀ hp]; ring_nf
        have e3 : ((-1 : ℂ)) ^ (r + (k - r - j)) = (-1) ^ (k - r - j) * (-1) ^ r := by
          rw [zpow_add₀ (by norm_num)]; ring
        rw [e3, e2]
        linear_combination (sgnC r * (-1) ^ r * cp ^ r * (-1) ^ (k - r - j)) * e1
    · have h2 : ¬ cone2 r j := fun h => hc h.1
      rw [if_neg h2, aaF_apply, if_neg hc, mul_zero, mul_zero]

noncomputable def aaEv2 {a β : ℤ} (hlo : -N < a + β) (hhi : a + β < N) (cx cp : ℂ) :
    SummableFamily ℤ ℂ ℤ :=
  rowFam (SummableFamily.Equiv e3
    (SummableFamily.mul (thF hN (a + β) (cx * cp)) (asF2 hN hlo hhi cx cp)))

lemma aaEv2_apply {a β : ℤ} (hlo : -N < a + β) (hhi : a + β < N) {cx cp : ℂ} (hx : cx ≠ 0)
    (hp : cp ≠ 0) (k : ℤ) : aaEv2 hN hlo hhi cx cp k = (mono β cp) ^ k * hs (aaF1 hN a cx k) := by
  refine hsum_reindex _ _ (Equiv.refl _) _ fun ⟨r, j⟩ => ?_
  simp only [Equiv.refl_apply, row_apply, SummableFamily.Equiv_toFun, SummableFamily.mul_toFun]
  rw [show e3.symm (k, (r, j)) = (k - r - j, (r, j)) from rfl, thF_apply]
  exact aa_eval_pt2 hN hlo hhi hx hp k r j

lemma aaEv2_sum {a β : ℤ} (hlo : -N < a + β) (hhi : a + β < N) (cx cp : ℂ) :
    hs (aaEv2 hN hlo hhi cx cp) = θ hN (a + β) (cx * cp) * Aser2 hN hlo hhi cx cp := by
  rw [aaEv2, hs_rowFam, hs_eq, SummableFamily.hsum_equiv, SummableFamily.hsum_mul]
  rfl

/-- the evaluation family `k ↦ p^k 𝒜_k`, valid for `−N < val(xp) < N`. -/
noncomputable def AAev {a β : ℤ} (hlo : -N < a + β) (hhi : a + β < N) (cx cp : ℂ) :
    SummableFamily ℤ ℂ ℤ :=
  aaEv2 hN hlo hhi cx cp + (-mono β cp) • SummableFamily.Equiv (Equiv.addRight 1) (sqF hN (a + β) (cx * cp))

theorem AAev_apply {a β : ℤ} (hlo : -N < a + β) (hhi : a + β < N) {cx cp : ℂ} (hx : cx ≠ 0)
    (hp : cp ≠ 0) (k : ℤ) : AAev hN hlo hhi cx cp k = (mono β cp) ^ k * AA hN a cx k := by
  simp only [AAev, SummableFamily.add_apply, SummableFamily.smul_apply, HahnSeries.of_symm_smul_of_eq_mul,
    SummableFamily.Equiv_toFun, Equiv.addRight_symm_apply, sqF_apply]
  rw [aaEv2_apply hN hlo hhi hx hp, AA_split hN]
  simp only [mono_zpow]
  have key : mono β cp * mono ((a + β) * (k - 1)) ((cx * cp) ^ (k - 1)) =
      mono (k * β) (cp ^ k) * mono (a * (k - 1)) (cx ^ (k - 1)) := by
    rw [mono_mul, mono_mul]
    congr 1
    · ring
    · rw [mul_zpow]
      conv_rhs => rw [show k = 1 + (k - 1) by ring, zpow_add₀ hp, zpow_one]
      ring
  try rw [show k + -1 = k - 1 by ring]
  linear_combination (-Θlo hN (k - 1)) * key

/-- **evaluation at a general point**: `Σ_k p^k 𝒜_k = θ(xp) A(x,p)` for `−N < val(xp) < N`, `xp ≠ 1`. -/
theorem AAev_sum {a β : ℤ} (hlo : -N < a + β) (hhi : a + β < N) {cx cp : ℂ} (hxp : cx * cp ≠ 0)
    (h1 : mono (a + β) (cx * cp) ≠ 1) :
    hs (AAev hN hlo hhi cx cp) = θ hN (a + β) (cx * cp) * Ab hN hlo hhi cx cp := by
  have hq := sq_eval hN (a + β) hxp
  have hne : (1 : L) - mono (a + β) (cx * cp) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hsq : hs (sqF hN (a + β) (cx * cp)) = θ hN (a + β) (cx * cp) * (1 - mono (a + β) (cx * cp))⁻¹ := by
    rw [← hq]; field_simp
  rw [AAev, hs_eq, SummableFamily.hsum_add, SummableFamily.hsum_smul, SummableFamily.hsum_equiv,
    ← hs_eq, ← hs_eq, aaEv2_sum, hsq, Ab]
  ring

end ExtEval


/-! ## `θ(qᵐ) = 0` -/

section ThetaQpow
variable {N : ℕ} (hN : 1 ≤ N)
include hN

/-- `θ(qᵐ) = 0`. -/
theorem θ_qpow (m : ℤ) : θ hN (N * m) 1 = 0 := by
  have h := hsum_reindex (thF hN (N * m) 1) (thF hN (N * m) 1) (Equiv.subLeft (1 - 2 * m)) (-1) fun j => by
    simp only [thF_apply, thT, Equiv.subLeft_apply, thE, thC, one_zpow, mul_one]
    have ex : (N : ℤ) * c2 (1 - 2 * m - j) + N * m * (1 - 2 * m - j) = N * c2 j + N * m * j := by
      have h1 := two_c2 (1 - 2 * m - j); have h2 := two_c2 j
      have : c2 (1 - 2 * m - j) + m * (1 - 2 * m - j) = c2 j + m * j := by nlinarith
      linear_combination (N : ℤ) * this
    have ec : ((-1 : ℂ)) ^ (1 - 2 * m - j) = -(-1) ^ j := by
      rw [show 1 - 2 * m - j = 1 - (2 * m + j) by ring, zpow_neg_one_one_sub, zpow_add₀ (by norm_num),
        show ((2 : ℤ) * m) = m + m by ring, zpow_add₀ (by norm_num), ← mul_zpow]
      norm_num
    rw [ex, ec, mono, mono, single_neg]
    exact (neg_one_mul _).symm
  have h2 : (2 : L) * θ hN (N * m) 1 = 0 := by unfold θ; rw [two_mul]; nth_rw 1 [h]; ring
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exfalso
    rw [← one_add_one_eq_two] at h3
    have := congrArg (fun f : L => f.coeff 0) h3
    simp only [coeff_add, coeff_one, if_true, coeff_zero] at this
    norm_num at this
  · exact h3

end ThetaQpow


/-! ## The constant `κ(x) = θ(x)A(x,1) = Σ_u u(−1)^u q^{C(u,2)}` -/

section Kappa

/-- a family value, typed in `L`. -/
noncomputable def sv {ι : Type*} (s : SummableFamily ℤ ℂ ι) (i : ι) : L := s i

lemma hsum_reindex' {ι κ : Type*} (s : SummableFamily ℤ ℂ ι) (t : SummableFamily ℤ ℂ κ) (σ : ι ≃ κ) (a : L)
    (h : ∀ i, sv t (σ i) = a * sv s i) : hs t = a * hs s := hsum_reindex s t σ a h

lemma c2_shift (r j k : ℤ) : c2 (r + j) + c2 k - k * j = c2 r + c2 (k - j) + (r - 1) * j := by
  have h1 := two_c2 (r + j); have h2 := two_c2 k; have h3 := two_c2 r; have h4 := two_c2 (k - j)
  nlinarith

lemma cone_abs {r j : ℤ} (h : cone r j) : |j| ≤ |r + j| := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg h2, abs_of_nonneg (by omega)]; omega
  · rw [abs_of_neg (by omega), abs_of_neg (by omega)]; omega

variable (N : ℕ)

/-- exponent of the `κ`-family. -/
def kE (k : ℤ) (rj : ℤ × ℤ) : ℤ :=
  if cone rj.1 rj.2 then N * (c2 (rj.1 + rj.2) + c2 k - k * rj.2) else |rj.1| + |rj.2|

noncomputable def kC (k : ℤ) (rj : ℤ × ℤ) : ℂ :=
  if cone rj.1 rj.2 then sgnC rj.1 * (-1) ^ (rj.1 + k - rj.2) else 0

variable {N}

lemma kE_lb (hN : 1 ≤ N) (k : ℤ) (rj : ℤ × ℤ) : -(N * ((|k| + 1) * (|k| + 1))) ≤ kE N k rj := by
  unfold kE
  have hN' : (0 : ℤ) ≤ N := by positivity
  split_ifs with hc
  · have h1 := cone_abs hc
    have h2 := c2_sub_bound k (rj.1 + rj.2)
    have h3 := c2_nonneg k
    have h4 : -(|k| * |rj.1 + rj.2|) ≤ -(k * rj.2) := by
      have := le_abs_self (k * rj.2); rw [abs_mul] at this
      nlinarith [abs_nonneg k]
    have : -((|k| + 1) * (|k| + 1)) ≤ c2 (rj.1 + rj.2) + c2 k - k * rj.2 := by linarith
    nlinarith
  · have := abs_nonneg rj.1; have := abs_nonneg rj.2; nlinarith

lemma kE_fin (hN : 1 ≤ N) (k n : ℤ) : {rj : ℤ × ℤ | kE N k rj = n}.Finite := by
  set U := 2 * |k| + 1 + 2 * |n|
  set B := |n| + 2 * U
  refine ((Set.finite_Icc (-B) B).prod (Set.finite_Icc (-B) B)).subset fun ⟨r, j⟩ h => ?_
  simp only [Set.mem_setOf_eq, kE] at h
  have hn := abs_nonneg n; have hk := abs_nonneg k
  have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
  split_ifs at h with hc
  · have h1 := cone_abs hc
    have h3 := c2_nonneg k
    have h4 : -(|k| * |r + j|) ≤ -(k * j) := by
      have := le_abs_self (k * j); rw [abs_mul] at this
      nlinarith [abs_nonneg k]
    have h5 : c2 (r + j) - |k| * |r + j| ≤ |n| := by
      have h6 : 0 ≤ c2 (r + j) + c2 k - k * j := by
        rw [c2_shift]
        have := cone_mul_nonneg hc; have := c2_nonneg r; have := c2_nonneg (k - j); linarith
      have : c2 (r + j) + c2 k - k * j ≤ N * (c2 (r + j) + c2 k - k * j) := le_mul_of_one_le_left h6 hN'
      have := le_abs_self n
      linarith
    have hu := c2_sub_le k (r + j) |n| h5
    rw [abs_abs] at hu
    have hr : |r| ≤ |r + j| + |j| := by
      have := abs_sub (r + j) j; rwa [show r + j - j = r by ring] at this
    simp only [Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> [have := neg_abs_le r; have := le_abs_self r;
      have := neg_abs_le j; have := le_abs_self j] <;> linarith
  · have hr := abs_nonneg r; have hj := abs_nonneg j
    have h1 : |r| ≤ |n| := by rw [← h]; have := le_abs_self (|r| + |j|); linarith
    have h2 : |j| ≤ |n| := by rw [← h]; have := le_abs_self (|r| + |j|); linarith
    simp only [Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> [have := neg_abs_le r; have := le_abs_self r;
      have := neg_abs_le j; have := le_abs_self j] <;> nlinarith

/-- `K_k = Σ_cone sgn(r) (−1)^{r+k−j} q^{C(r+j,2)+C(k,2)−kj}` (the `x^k`-coefficient of `θ(x)A(x,1)`). -/
noncomputable def kF (hN : 1 ≤ N) (k : ℤ) : SummableFamily ℤ ℂ (ℤ × ℤ) :=
  monoFam (kE N k) (kC k) _ (kE_lb hN k) (kE_fin hN k)

lemma kF_apply (hN : 1 ≤ N) (k : ℤ) (rj : ℤ × ℤ) :
    kF hN k rj = if cone rj.1 rj.2 then
      mono (N * (c2 (rj.1 + rj.2) + c2 k - k * rj.2)) (sgnC rj.1 * (-1) ^ (rj.1 + k - rj.2)) else 0 := by
  rw [kF, monoFam_apply, kE, kC]
  split_ifs <;> simp [mono]


lemma kScalar (r j : ℤ) :
    ((if cone r j then sgnC r else 0) - (if cone (r + 1) (j - 1) then sgnC (r + 1) else 0) : ℂ) =
      (if j = 0 then 1 else 0) - (if r = 0 then 1 else 0) := by
  unfold cone sgnC
  split_ifs <;> norm_num <;> omega

def rowE : ℤ ↪ ℤ × ℤ := ⟨fun r => (r, 0), fun _ _ h => (Prod.mk.inj h).1⟩
def colE : ℤ ↪ ℤ × ℤ := ⟨fun j => (0, j), fun _ _ h => (Prod.mk.inj h).2⟩

/-- `(r, j) ↦ (r − 1, j + 1)`. -/
def diagShift : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun p := (p.1 - 1, p.2 + 1)
  invFun p := (p.1 + 1, p.2 - 1)
  left_inv p := by simp
  right_inv p := by simp

/-- **`K_k = 0` for `k ≠ 0`** (telescoping along `(r,j) ↦ (r−1,j+1)`). -/
theorem kF_zero (hN : 1 ≤ N) {k : ℤ} (hk : k ≠ 0) : hs (kF hN k) = 0 := by
  set c := mono (N * c2 k) ((-1 : ℂ) ^ k)
  set lineJ := (c • thF hN 0 1).embDomain rowE
  set lineR := (c • thF hN (N * (-k)) 1).embDomain colE
  set G := SummableFamily.Equiv diagShift (mono (-(N * k)) 1 • kF hN k)
  have hD : ∀ b, (kF hN k - G) b = (lineJ - lineR) b := by
    rintro ⟨r, j⟩
    have hG : G (r, j) = mono (N * (c2 (r + j) + c2 k - k * j))
        ((if cone (r + 1) (j - 1) then sgnC (r + 1) else 0) * (-1) ^ (r + k - j)) := by
      simp only [G, SummableFamily.Equiv_toFun, SummableFamily.smul_apply,
        HahnSeries.of_symm_smul_of_eq_mul]
      rw [show diagShift.symm (r, j) = (r + 1, j - 1) from rfl, kF_apply]
      simp only
      split_ifs with hc
      · rw [mono_mul]
        congr 1
        · rw [show r + 1 + (j - 1) = r + j by ring]; ring
        · rw [show r + 1 + k - (j - 1) = (r + k - j) + 2 by ring, neg_one_zpow_add_two]; ring
      · simp [mono]
    have hK : kF hN k (r, j) = mono (N * (c2 (r + j) + c2 k - k * j))
        ((if cone r j then sgnC r else 0) * (-1) ^ (r + k - j)) := by
      rw [kF_apply]; simp only; split_ifs <;> simp [mono]
    have hJ : lineJ (r, j) = mono (N * (c2 (r + j) + c2 k - k * j))
        ((if j = 0 then 1 else 0) * (-1) ^ (r + k - j)) := by
      by_cases hj : j = 0
      · subst hj
        rw [show ((r, (0 : ℤ)) : ℤ × ℤ) = rowE r from rfl]
        simp only [lineJ, SummableFamily.embDomain_image, SummableFamily.smul_apply,
          HahnSeries.of_symm_smul_of_eq_mul, thF_apply, thT, c, mono_mul, if_true, one_mul]
        congr 1
        · unfold thE; simp; ring
        · unfold thC; rw [one_zpow, mul_one, ← zpow_add₀ (by norm_num)]; ring_nf
      · rw [SummableFamily.embDomain_notin_range, if_neg hj, zero_mul]
        · simp [mono]
        · rintro ⟨r', hr'⟩; exact hj (congrArg Prod.snd hr').symm
    have hR : lineR (r, j) = mono (N * (c2 (r + j) + c2 k - k * j))
        ((if r = 0 then 1 else 0) * (-1) ^ (r + k - j)) := by
      by_cases hr : r = 0
      · subst hr
        rw [show (((0 : ℤ), j) : ℤ × ℤ) = colE j from rfl]
        simp only [lineR, SummableFamily.embDomain_image, SummableFamily.smul_apply,
          HahnSeries.of_symm_smul_of_eq_mul, thF_apply, thT, c, mono_mul, if_true, one_mul]
        congr 1
        · unfold thE; simp; ring
        · unfold thC
          rw [one_zpow, mul_one, show (0 : ℤ) + k - j = k + (-j) by ring, zpow_add₀ (by norm_num),
            zpow_neg, ← inv_zpow, inv_neg, inv_one]
      · rw [SummableFamily.embDomain_notin_range, if_neg hr, zero_mul]
        · simp [mono]
        · rintro ⟨j', hj'⟩; exact hr (congrArg Prod.fst hj').symm
    rw [SummableFamily.sub_apply, SummableFamily.sub_apply, hK, hG, hJ, hR, mono, mono, mono, mono,
      ← single_sub, ← single_sub, ← sub_mul, ← sub_mul, kScalar]
  have hsum := hsum_congr _ _ hD
  rw [hs_eq, hs_eq, SummableFamily.hsum_sub, SummableFamily.hsum_sub, SummableFamily.hsum_embDomain,
    SummableFamily.hsum_embDomain, SummableFamily.hsum_smul, SummableFamily.hsum_smul,
    SummableFamily.hsum_equiv, SummableFamily.hsum_smul] at hsum
  have t1 := θ_one hN
  have t2 := θ_qpow hN (-k)
  rw [θ, hs_eq] at t1 t2
  simp only [t1, t2, mul_zero, sub_zero] at hsum
  rw [← hs_eq] at hsum
  have hne : (1 : L) - mono (-(N * k)) 1 ≠ 0 := by
    intro h
    have := congrArg (fun f : L => f.coeff 0) h
    have hNk : -((N : ℤ) * k) ≠ 0 := by
      have : (N : ℤ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
      exact neg_ne_zero.mpr (mul_ne_zero this hk)
    simp [mono, coeff_single_of_ne (Ne.symm hNk)] at this
  have : (1 - mono (-(N * k)) 1) * hs (kF hN k) = 0 := by rw [sub_mul, one_mul]; exact hsum
  exact (mul_eq_zero.mp this).resolve_left hne


/-- `K_k` without its `r = 1` slice. -/
noncomputable def kF2 (hN : 1 ≤ N) (k : ℤ) : SummableFamily ℤ ℂ (ℤ × ℤ) :=
  monoFam (kE N k) (fun rj => if rj.1 = 1 then 0 else kC k rj) _ (kE_lb hN k) (kE_fin hN k)

lemma hs_kF_row1 (hN : 1 ≤ N) (k : ℤ) : hs (row (kF hN k) 1) = -Θlo hN k := by
  have := hsum_reindex' (thInd hN (· ≤ k)) (row (kF hN k) 1) (Equiv.subLeft k) (-1) fun i => by
    simp only [sv, row_apply, Equiv.subLeft_apply, kF_apply, thInd, monoFam_apply]
    by_cases hi : i ≤ k
    · have hc : cone 1 (k - i) := Or.inl ⟨le_rfl, by omega⟩
      rw [if_pos hc, if_pos hi]
      have ex : (N : ℤ) * (c2 (1 + (k - i)) + c2 k - k * (k - i)) = thE N 0 i := by
        unfold thE; have := c2_shift 1 (k - i) k; rw [show k - (k - i) = i by ring] at this
        simp only [c2, mul_zero, Int.zero_ediv, zero_add, sub_self, zero_mul, add_zero] at this ⊢
        rw [this]
      have ec : sgnC 1 * ((-1 : ℂ)) ^ (1 + k - (k - i)) = -(-1) ^ i := by
        unfold sgnC; rw [if_pos le_rfl, show 1 + k - (k - i) = i + 1 by ring, zpow_add₀ (by norm_num)]; ring
      rw [ex, ec, mono, mono, single_neg]
      exact (neg_one_mul (α := L) _).symm
    · have hc : ¬ cone 1 (k - i) := by unfold cone; omega
      rw [if_neg hc, if_neg hi]; simp [mono]
  rw [this, Θlo]; ring

lemma hs_kF_split (hN : 1 ≤ N) (k : ℤ) : hs (kF2 hN k) = hs (kF hN k) + Θlo hN k := by
  have h : ∀ rj, kF hN k rj = (kF2 hN k + (row (kF hN k) 1).embDomain slice1) rj := by
    rintro ⟨r, j⟩
    simp only [SummableFamily.add_apply]
    by_cases hr : r = 1
    · subst hr
      have he : ((row (kF hN k) 1).embDomain slice1) (slice1 j) = row (kF hN k) 1 j :=
        SummableFamily.embDomain_image _ _
      change _ = _ + ((row (kF hN k) 1).embDomain slice1) (slice1 j)
      rw [he]
      simp [kF2, mono, row_apply]
    · rw [SummableFamily.embDomain_notin_range, add_zero]
      · simp only [kF, kF2, monoFam_apply, if_neg hr]
      · rintro ⟨j', hj'⟩; exact hr (congrArg Prod.fst hj').symm
  have := hsum_congr _ _ h
  rw [hs_eq, hs_eq, SummableFamily.hsum_add, SummableFamily.hsum_embDomain, ← hs_eq (kF2 hN k),
    ← hs_eq (kF hN k), ← hs_eq (row (kF hN k) 1), hs_kF_row1] at this
  rw [this]; ring

/-- `(i, (r, j)) ↦ (i + j, (r, j))`. -/
def eK : ℤ × (ℤ × ℤ) ≃ ℤ × (ℤ × ℤ) where
  toFun p := (p.1 + p.2.2, p.2)
  invFun p := (p.1 - p.2.2, p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

lemma kappa_pt (hN : 1 ≤ N) {a : ℤ} (hlo : -N < a + 0) (hhi : a + 0 < N) {cx : ℂ} (hx : cx ≠ 0) (k r j : ℤ) :
    thT N a cx (k - j) * asF2 hN hlo hhi cx 1 (r, j) = mono (a * k) (cx ^ k) * kF2 hN k (r, j) := by
  rw [asF2_apply, kF2, monoFam_apply]
  simp only [kE, kC]
  by_cases hr : r = 1
  · have : ¬ cone2 r j := fun h => h.2 hr
    rw [if_neg this, if_pos hr, mul_zero]; simp [mono]
  · rw [if_neg hr]
    by_cases hc : cone r j
    · rw [if_pos ⟨hc, hr⟩, if_pos hc, if_pos hc, thT, mono_mul, mono_mul]
      congr 1
      · unfold thE asExp; have := c2_shift r j k; nlinarith
      · unfold thC
        rw [one_zpow, mul_one, mul_one, ← mul_assoc, show ((-1 : ℂ)) ^ (r + k - j) = (-1) ^ (k - j) * (-1) ^ r by
          rw [← zpow_add₀ (by norm_num)]; ring_nf,
          show cx ^ k = cx ^ (k - j) * cx ^ j by rw [← zpow_add₀ hx]; ring_nf]
        ring
    · rw [if_neg (fun h => hc h.1), mul_zero]; simp [mono, hc]

/-- **`κ(x) = θ(x) A(x,1) = K₀`**, independent of `x` (`−N < val x < N`, `x ≠ 1`). -/
theorem kappa_eq (hN : 1 ≤ N) {a : ℤ} (hlo : -N < a + 0) (hhi : a + 0 < N) {cx : ℂ} (hx : cx ≠ 0)
    (h1 : mono a cx ≠ 1) : θ hN a cx * Ab hN hlo hhi cx 1 = hs (kF hN 0) := by
  set P := SummableFamily.Equiv eK (SummableFamily.mul (thF hN a cx) (asF2 hN hlo hhi cx 1))
  have hrow : ∀ k, rowFam P k = mono (a * k) (cx ^ k) * (hs (kF hN k) + Θlo hN k) := by
    intro k
    rw [← hs_kF_split]
    refine hsum_reindex _ _ (Equiv.refl _) _ fun ⟨r, j⟩ => ?_
    simp only [Equiv.refl_apply, row_apply, P, SummableFamily.Equiv_toFun, SummableFamily.mul_toFun]
    rw [show eK.symm (k, (r, j)) = (k - j, (r, j)) from rfl, thF_apply]
    exact kappa_pt hN hlo hhi hx k r j
  have hP : hs (rowFam P) = θ hN a cx * Aser2 hN hlo hhi cx 1 := by
    rw [hs_rowFam, hs_eq, SummableFamily.hsum_equiv, SummableFamily.hsum_mul]; rfl
  have hD : ∀ k, (rowFam P - sqF hN a cx) k = SummableFamily.single (0 : ℤ) (hs (kF hN 0)) k := by
    intro k
    rw [SummableFamily.sub_apply, hrow, sqF_apply, mul_add, add_sub_cancel_right]
    change _ = (Pi.single (0 : ℤ) (hs (kF hN 0)) : ℤ → L) k
    by_cases hk : k = 0
    · subst hk; simp [mono]
    · rw [kF_zero hN hk, mul_zero, Pi.single_apply, if_neg hk]
  have := hsum_congr _ _ hD
  rw [hs_eq, hs_eq, SummableFamily.hsum_sub, SummableFamily.hsum_single, ← hs_eq, ← hs_eq, hP] at this
  have hq := sq_eval hN a hx
  have hne : (1 : L) - mono a cx ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  rw [Ab, show mono (a + 0) (cx * 1) = mono a cx by simp, show mono 0 (1 : ℂ) = 1 from rfl, ← this]
  field_simp
  rw [← hq]; ring

end Kappa


/-! ## Change of `z` at general points -/

section Main2
variable {N : ℕ} (hN : 1 ≤ N)
include hN

lemma G1 {a : ℤ} (h1 : -N < a) (h2 : a < N) (m : ℤ) : -max 0 (-a) ≤ thE (2 * N) (2 * 0 + a) m := by
  rw [thE2]
  have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
  have hmx1 : 0 ≤ max 0 (-a) := le_max_left _ _
  have hmx2 : -a ≤ max 0 (-a) := le_max_right _ _
  rcases lt_trichotomy m 0 with h | h | h
  · obtain ⟨u, rfl⟩ : ∃ u, m = -u := ⟨-m, by ring⟩
    have hu : 1 ≤ u := by omega
    have : 0 ≤ (N * (u + 1) - a) * u := mul_nonneg (by nlinarith) (by omega)
    nlinarith
  · subst h; simp
  · have : 0 ≤ (N : ℤ) * (m * (m - 1)) := mul_nonneg (by omega) (by nlinarith)
    rcases le_or_gt 0 a with ha | ha
    · nlinarith
    · rcases eq_or_lt_of_le (show 1 ≤ m by omega) with h' | h'
      · subst h'; simp; omega
      · have : 0 ≤ (N * (m - 1) + a) * m := mul_nonneg (by nlinarith) (by omega)
        nlinarith

lemma G2 {a b : ℤ} (hb1 : 1 ≤ a + b) (hb2 : a + b ≤ N - 1) (hb3 : 1 ≤ b) (hb4 : b ≤ N - 1) (m : ℤ) :
    1 + max 0 (-a) ≤ thE (2 * N) (N + 2 * b + a) m + b := by
  rw [thE2]
  have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
  have hM : max 0 (-a) ≤ b - 1 := max_le (by omega) (by omega)
  have hM' : max 0 (-a) ≤ N - a - b - 1 := max_le (by omega) (by omega)
  rcases lt_trichotomy m 0 with h | h | h
  · obtain ⟨u, rfl⟩ : ∃ u, m = -u := ⟨-m, by ring⟩
    have hu : 1 ≤ u := by omega
    rcases eq_or_lt_of_le hu with h' | h'
    · subst h'; nlinarith
    · have : 0 ≤ (N * u - 2 * b - a - 1) * u := mul_nonneg (by nlinarith) (by omega)
      nlinarith
  · subst h; simp; omega
  · have : 0 ≤ (N : ℤ) * (m * (m - 1)) := mul_nonneg (by omega) (by nlinarith)
    have : 0 ≤ (N + 2 * b + a) * m := mul_nonneg (by omega) (by omega)
    nlinarith

lemma quad_pos' {e : ℤ} (h0 : -N < e) (h1 : e < N) {m : ℤ} (hm : m ≠ 0) : 0 < thE (2 * N) (N + e) m := by
  rw [thE2]
  have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
  rcases lt_or_gt_of_ne hm with h | h
  · obtain ⟨u, rfl⟩ : ∃ u, m = -u := ⟨-m, by ring⟩
    have hu : 1 ≤ u := by omega
    have : 0 < (N * u - e) * u := mul_pos (by nlinarith) (by omega)
    nlinarith
  · have : 0 ≤ (N : ℤ) * (m * (m - 1)) := mul_nonneg (by omega) (by nlinarith)
    have : 0 < (N + e) * m := mul_pos (by omega) h
    nlinarith

/-- the determinant at the auxiliary point `z₀` (general `x`). -/
theorem det_ne2 {a b₀ : ℤ} (ha1 : -N < a) (ha2 : a < N) (hb1 : 1 ≤ a + b₀) (hb2 : a + b₀ ≤ N - 1)
    (hb3 : 1 ≤ b₀) (hb4 : b₀ ≤ N - 1) (cx : ℂ) {c₀ : ℂ} :
    hs (e0M hN a cx 0 1) * hs (e1M hN a cx b₀ c₀) - hs (e0M hN a cx b₀ c₀) * hs (e1M hN a cx 0 1) ≠ 0 := by
  have Pb : ∀ n < -max 0 (-a), (hs (e0M hN a cx 0 1)).coeff n = 0 := by
    unfold e0M; exact lowerAll _ _ _ _ _ _ (G1 hN ha1 ha2)
  have Sb : ∀ n < 1 + max 0 (-a), (hs (e1M hN a cx b₀ c₀)).coeff n = 0 := by
    unfold e1M; exact lowerAll _ _ _ _ _ _ (G2 hN hb1 hb2 hb3 hb4)
  obtain ⟨R0, Rb⟩ := e0M_low hN (β := b₀) (a := a) cx c₀ (by omega) (by omega)
  have hQ : (hs (e1M hN a cx 0 1)).coeff 0 = 1 ∧ ∀ n < 0, (hs (e1M hN a cx 0 1)).coeff n = 0 := by
    refine ⟨?_, fun n hn => monoFam_coeff_zero _ _ _ _ _ _ fun m => ?_⟩
    · unfold e1M
      rw [monoFam_coeff_at _ _ _ _ _ 0 0 (by simp [thE_zero]) fun m hm => by
        have := quad_pos' hN (e := a) ha1 ha2 hm; simp only [mul_zero, add_zero] at this ⊢; omega]
      simp
    · rcases eq_or_ne m 0 with rfl | hm
      · simp [thE_zero]; omega
      · have := quad_pos' hN (e := a) ha1 ha2 hm; simp only [mul_zero, add_zero] at this ⊢; omega
  obtain ⟨Q0, Qb⟩ := hQ
  intro hΔ
  have := congrArg (fun f : L => f.coeff 0) hΔ
  simp only [coeff_sub, coeff_zero] at this
  have e := coeff_mul_lowest _ _ 0 0 Rb Qb
  rw [add_zero] at e
  rw [coeff_mul_below _ _ _ _ Pb Sb _ (by omega), e, R0, Q0] at this
  norm_num at this

lemma θ_ne {e : ℤ} (h0 : 0 < e) (h1 : e < N) (c : ℂ) : θ hN e c ≠ 0 := by
  intro h
  have := congrArg (fun f : L => f.coeff 0) h
  simp only [coeff_zero] at this
  rw [θ, thF, monoFam_coeff_at _ _ _ _ _ 0 0 (by simp [thE, c2]) fun k hk => ?_] at this
  · simp [thC] at this
  · unfold thE
    have h2 := two_c2 k
    have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
    rcases lt_or_gt_of_ne hk with h | h
    · obtain ⟨u, rfl⟩ : ∃ u, k = -u := ⟨-k, by ring⟩
      have : 0 < (N * (u + 1) - 2 * e) * u := mul_pos (by nlinarith) (by omega)
      nlinarith
    · have : 0 ≤ (N : ℤ) * (k * (k - 1)) := mul_nonneg (by omega) (by nlinarith)
      have : 0 < e * k := mul_pos h0 h
      nlinarith


theorem sol_vanish2 {a b₀ : ℤ} (ha1 : -N < a) (ha2 : a < N) (hb1 : 1 ≤ a + b₀) (hb2 : a + b₀ ≤ N - 1)
    (hb3 : 1 ≤ b₀) (hb4 : b₀ ≤ N - 1) {cx c₀ : ℂ} (hx : cx ≠ 0) (hc0 : c₀ ≠ 0)
    (F : ℤ → L) (hF : ∀ k, F (k + 2) = mult N a cx k * F k)
    (S₁ S₀ : SummableFamily ℤ ℂ ℤ) (hS₁ : ∀ k, S₁ k = (mono 0 1) ^ k * F k)
    (hS₀ : ∀ k, S₀ k = (mono b₀ c₀) ^ k * F k) (e₁ : hs S₁ = 0) (e₀ : hs S₀ = 0) : ∀ k, F k = 0 := by
  have d₁ := ev_decomp hN a hx F hF 0 one_ne_zero S₁ hS₁
  have d₀ := ev_decomp hN a hx F hF b₀ hc0 S₀ hS₀
  rw [e₁, hs_e0Fam, hs_e1Fam] at d₁
  rw [e₀, hs_e0Fam, hs_e1Fam] at d₀
  have hΔ := det_ne2 hN ha1 ha2 hb1 hb2 hb3 hb4 cx (c₀ := c₀)
  set P := hs (e0M hN a cx 0 1); set Q := hs (e1M hN a cx 0 1)
  set R := hs (e0M hN a cx b₀ c₀); set S := hs (e1M hN a cx b₀ c₀)
  have f0 : F 0 * (P * S - R * Q) = 0 := by linear_combination (-S) * d₁ + Q * d₀
  have f1 : F 1 * (P * S - R * Q) = 0 := by linear_combination R * d₁ - P * d₀
  have z0 := (mul_eq_zero.mp f0).resolve_right hΔ
  have z1 := (mul_eq_zero.mp f1).resolve_right hΔ
  intro k
  rw [sol_basis hx F hF k, z0, z1]; ring

noncomputable def Fev2 {a b₀ β : ℤ} (hlo : -N < a + β) (hhi : a + β < N) (cx c₀ : ℂ) (m₀ cc : L) (cp : ℂ) :
    SummableFamily ℤ ℂ ℤ :=
  AAev hN hlo hhi cx cp - m₀ • ttEv hN 0 1 a cx β cp + cc • ttEv hN (-b₀) c₀⁻¹ (a + b₀) (cx * c₀) β cp

lemma Fev2_apply {a b₀ β : ℤ} (hlo : -N < a + β) (hhi : a + β < N) {cx c₀ : ℂ} (hx : cx ≠ 0)
    (m₀ cc : L) {cp : ℂ} (hp : cp ≠ 0) (k : ℤ) :
    Fev2 hN (b₀ := b₀) hlo hhi cx c₀ m₀ cc cp k = (mono β cp) ^ k *
      (AA hN a cx k - m₀ * TT hN 0 1 a cx k + cc * TT hN (-b₀) c₀⁻¹ (a + b₀) (cx * c₀) k) := by
  simp only [Fev2, SummableFamily.add_apply, SummableFamily.sub_apply, SummableFamily.smul_apply,
    HahnSeries.of_symm_smul_of_eq_mul]
  rw [AAev_apply hN hlo hhi hx hp, ttEv_apply hN _ _ _ _ _ hp, ttEv_apply hN _ _ _ _ _ hp]
  ring

lemma Fev2_sum {a b₀ β : ℤ} (hlo : -N < a + β) (hhi : a + β < N) {cx c₀ : ℂ} (m₀ cc : L) {cp : ℂ}
    (hxp : cx * cp ≠ 0) (h1 : mono (a + β) (cx * cp) ≠ 1) :
    hs (Fev2 hN (b₀ := b₀) hlo hhi cx c₀ m₀ cc cp) =
      θ hN (a + β) (cx * cp) * Ab hN hlo hhi cx cp - m₀ * (θ hN (0 + β) (1 * cp) * θ hN (a + β) (cx * cp))
      + cc * (θ hN (-b₀ + β) (c₀⁻¹ * cp) * θ hN (a + b₀ + β) (cx * c₀ * cp)) := by
  rw [Fev2, hs_eq, SummableFamily.hsum_add, SummableFamily.hsum_sub, SummableFamily.hsum_smul,
    SummableFamily.hsum_smul, ← hs_eq, ← hs_eq, ← hs_eq, AAev_sum hN hlo hhi hxp h1, ttEv_sum, ttEv_sum]

/-- **Change of `z` at general points.** `x = c_x t^a` with `−N < a < N`, `x ≠ 1` (e.g. a root of
unity); `z₀ = c₀ t^{b₀}` an auxiliary interior point; `z₁ = c₁ t^{b₁}` any point with
`−N < val(xz₁) < N`, `xz₁ ≠ 1`. With `K₀ = θ(x)A(x,1)` (`kappa_eq`):
`θ(z₀)θ(xz₀)θ(xz₁)A(x,z₁) − A(x,z₀)θ(xz₀)θ(z₁)θ(xz₁) + z₀ K₀ θ(z₁/z₀)θ(xz₀z₁) = 0`. -/
theorem change_of_z2 {a b₀ b₁ : ℤ} (ha1 : -N < a) (ha2 : a < N) (hb1 : 1 ≤ a + b₀) (hb2 : a + b₀ ≤ N - 1)
    (hb3 : 1 ≤ b₀) (hb4 : b₀ ≤ N - 1) (hc0' : -N < a + b₁) (hcN : a + b₁ < N)
    {cx c₀ c₁ : ℂ} (hx : cx ≠ 0) (hc0 : c₀ ≠ 0) (hc1 : c₁ ≠ 0) (hx1 : mono a cx ≠ 1)
    (hxz1 : mono (a + b₁) (cx * c₁) ≠ 1) :
    θ hN b₀ c₀ * θ hN (a + b₀) (cx * c₀) * θ hN (a + b₁) (cx * c₁) * Ab hN hc0' hcN cx c₁
      - Ab hN (a := a) (β := b₀) (by omega) (by omega) cx c₀ * θ hN (a + b₀) (cx * c₀) * θ hN b₁ c₁ *
          θ hN (a + b₁) (cx * c₁)
      + mono b₀ c₀ * hs (kF hN 0) * θ hN (-b₀ + b₁) (c₀⁻¹ * c₁) * θ hN (a + b₀ + b₁) (cx * c₀ * c₁)
      = 0 := by
  have hθ₀ : θ hN b₀ c₀ ≠ 0 := θ_ne hN (by omega) (by omega) c₀
  have hθx₀ : θ hN (a + b₀) (cx * c₀) ≠ 0 := θ_ne hN (by omega) (by omega) _
  have hlo0 : -N < a + 0 := by omega
  have hhi0 : a + 0 < N := by omega
  have hlob : -N < a + b₀ := by omega
  have hhib : a + b₀ < N := by omega
  set κ := θ hN a cx * Ab hN hlo0 hhi0 cx 1 with hκ
  have hκ' : κ = hs (kF hN 0) := kappa_eq hN hlo0 hhi0 hx hx1
  set m₀ := Ab hN hlob hhib cx c₀ / θ hN b₀ c₀ with hm₀
  set cc := mono b₀ c₀ * κ / (θ hN b₀ c₀ * θ hN (a + b₀) (cx * c₀)) with hcc
  set F : ℤ → L := fun k => AA hN a cx k - m₀ * TT hN 0 1 a cx k + cc * TT hN (-b₀) c₀⁻¹ (a + b₀) (cx * c₀) k
  have hF : ∀ k, F (k + 2) = mult N a cx k * F k := by
    intro k
    simp only [F]
    rw [AA_rec hN a hx, TT_rec hN 0 one_ne_zero a hx, TT_rec hN (-b₀) (inv_ne_zero hc0) (a + b₀)
      (mul_ne_zero hx hc0)]
    have e1 : mono (N * k + (0 + a)) (1 * cx) = mult N a cx k := by simp [mult]
    have e2 : mono (N * k + (-b₀ + (a + b₀))) (c₀⁻¹ * (cx * c₀)) = mult N a cx k := by
      unfold mult; congr 1
      · ring
      · field_simp
    rw [e1, e2, show mono (N * k + a) cx = mult N a cx k from rfl]
    ring
  have hm0' : m₀ * θ hN b₀ c₀ = Ab hN hlob hhib cx c₀ := by rw [hm₀]; field_simp
  have key : cc * (θ hN b₀ c₀ * θ hN (a + b₀) (cx * c₀)) = mono b₀ c₀ * κ := by rw [hcc]; field_simp
  have hxne : mono (a + 0) (cx * 1) ≠ 1 := by simpa using hx1
  have hxz0 : mono (a + b₀) (cx * c₀) ≠ 1 := by
    intro h; have := congrArg (fun f : L => f.coeff 0) h
    simp [mono, coeff_single_of_ne (show (0 : ℤ) ≠ a + b₀ by omega)] at this
  have z₁ : hs (Fev2 hN (b₀ := b₀) hlo0 hhi0 cx c₀ m₀ cc 1) = 0 := by
    rw [Fev2_sum hN hlo0 hhi0 m₀ cc (by simpa using hx) hxne]
    simp only [add_zero, mul_one]
    rw [θ_one hN, θ_inv hN b₀ hc0]
    have hmm : mono b₀ c₀ * mono (-b₀) c₀⁻¹ = 1 := by rw [mono_mul]; simp [hc0, mono]
    have hk : θ hN a cx * Ab hN hlo0 hhi0 cx 1 = κ := rfl
    rw [hk]
    linear_combination (-mono (-b₀) c₀⁻¹) * key - κ * hmm
  have z₀ : hs (Fev2 hN (b₀ := b₀) hlob hhib cx c₀ m₀ cc c₀) = 0 := by
    rw [Fev2_sum hN hlob hhib m₀ cc (mul_ne_zero hx hc0) hxz0]
    simp only [zero_add, one_mul]
    rw [show -b₀ + b₀ = 0 by ring, inv_mul_cancel₀ hc0, θ_one hN]
    linear_combination (-θ hN (a + b₀) (cx * c₀)) * hm0'
  have hall := sol_vanish2 hN ha1 ha2 hb1 hb2 hb3 hb4 hx hc0 F hF _ _
    (fun k => Fev2_apply hN (b₀ := b₀) hlo0 hhi0 hx m₀ cc one_ne_zero k)
    (fun k => Fev2_apply hN (b₀ := b₀) hlob hhib hx m₀ cc hc0 k) z₁ z₀
  have z₂ := ev_decomp hN a hx F hF b₁ hc1 _ (fun k => Fev2_apply hN (b₀ := b₀) hc0' hcN hx m₀ cc hc1 k)
  rw [hall 0, hall 1, zero_mul, zero_mul, add_zero, Fev2_sum hN hc0' hcN m₀ cc (mul_ne_zero hx hc1) hxz1] at z₂
  simp only [zero_add, one_mul] at z₂
  rw [← hκ']
  linear_combination (θ hN b₀ c₀ * θ hN (a + b₀) (cx * c₀)) * z₂
    + (θ hN (a + b₀) (cx * c₀) * θ hN b₁ c₁ * θ hN (a + b₁) (cx * c₁)) * hm0'
    - (θ hN (-b₀ + b₁) (c₀⁻¹ * c₁) * θ hN (a + b₀ + b₁) (cx * c₀ * c₁)) * key

end Main2

end ALz
