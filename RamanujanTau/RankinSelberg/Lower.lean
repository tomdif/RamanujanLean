/-
# Lower bound for `∫₀¹ |Δ(x + i/C²)|² dx` via Farey arcs

`integral_lower`: there is `m > 0` with `∫₀¹ |Δ(x + i/C²)|² dx ≥ (m/32) C²⁴` for every `C ≥ 1`.

The horocycle `Im z = 1/C²` is covered, with positive proportion, by the disjoint Farey
intervals `J(a,c) = [a/c − 1/(2cC), a/c − 1/(4cC)]` (`1 ≤ a ≤ c ≤ C`, `(a,c) = 1`); on each,
`|Δ|² ≥ m C²⁴` (`Band.lean`). There are at least `C²/8` such pairs
(`card_coprime_pairs_ge`: an elementary union bound using `∑_{d≥2} 1/d² ≤ 3/4`), each of length
`1/(4cC) ≥ 1/(4C²)`.
-/
import RamanujanTau.RankinSelberg.Band

set_option autoImplicit false

namespace RamanujanTau.RankinSelberg

open Complex ModularForm MeasureTheory Finset
open UpperHalfPlane hiding I
open scoped MatrixGroups Real

/-! ## Counting coprime pairs -/

lemma sum_inv_sq_le_aux (n : ℕ) (hn : 2 ≤ n) :
    ∑ d ∈ Icc 2 n, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 3 / 4 - 1 / n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have h : (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / n - 1 / ((n + 1 : ℕ) : ℝ) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    linarith

lemma sum_inv_sq_le (n : ℕ) : ∑ d ∈ Icc 2 n, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 3 / 4 := by
  rcases lt_or_ge n 2 with h | h
  · rw [Icc_eq_empty (by omega)]; norm_num
  · have := sum_inv_sq_le_aux n h
    have : (0 : ℝ) ≤ 1 / n := by positivity
    linarith

/-- The Farey pairs `1 ≤ a ≤ c ≤ C`, `gcd(a,c) = 1`. -/
def fareyPairs (C : ℕ) : Finset (ℕ × ℕ) :=
  ((Ioc 0 C) ×ˢ (Ioc 0 C)).filter (fun p => p.1 ≤ p.2 ∧ Nat.Coprime p.1 p.2)

/-- **At least `C²/8` Farey pairs.** -/
theorem card_fareyPairs_ge (C : ℕ) : ((C : ℝ)) ^ 2 ≤ 8 * (fareyPairs C).card := by
  classical
  set s := Ioc 0 C
  set Q := (s ×ˢ s).filter (fun p : ℕ × ℕ => Nat.Coprime p.1 p.2)
  set B := (s ×ˢ s).filter (fun p : ℕ × ℕ => ¬ Nat.Coprime p.1 p.2)
  have hQB : Q.card + B.card = C ^ 2 := by
    rw [card_filter_add_card_filter_not, card_product, Nat.card_Ioc]; simp [sq]
  -- union bound for the non-coprime pairs
  have hBsub : B ⊆ (Icc 2 C).biUnion (fun d => (s.filter (d ∣ ·)) ×ˢ (s.filter (d ∣ ·))) := by
    intro p hp
    simp only [B, s, mem_filter, mem_product, mem_Ioc] at hp
    obtain ⟨⟨⟨ha0, haC⟩, ⟨hc0, hcC⟩⟩, hnc⟩ := hp
    have hg1 : 1 ≤ Nat.gcd p.1 p.2 := Nat.gcd_pos_of_pos_left _ ha0
    have hg2 : 2 ≤ Nat.gcd p.1 p.2 := by
      rcases Nat.lt_or_ge (Nat.gcd p.1 p.2) 2 with h | h
      · exact absurd (by omega : Nat.gcd p.1 p.2 = 1) hnc
      · exact h
    have hgC : Nat.gcd p.1 p.2 ≤ C := (Nat.gcd_le_left _ ha0).trans haC
    simp only [mem_biUnion, mem_Icc, mem_product, mem_filter, s, mem_Ioc]
    exact ⟨Nat.gcd p.1 p.2, ⟨hg2, hgC⟩, ⟨⟨ha0, haC⟩, Nat.gcd_dvd_left _ _⟩,
      ⟨⟨hc0, hcC⟩, Nat.gcd_dvd_right _ _⟩⟩
  have hBcard : (B.card : ℝ) ≤ 3 / 4 * (C : ℝ) ^ 2 := by
    have h1 := card_le_card hBsub
    have h2 := card_biUnion_le (s := Icc 2 C)
      (t := fun d => (s.filter (d ∣ ·)) ×ˢ (s.filter (d ∣ ·)))
    have h3 : (B.card : ℝ) ≤ ∑ d ∈ Icc 2 C, ((C / d : ℕ) : ℝ) ^ 2 := by
      have : B.card ≤ ∑ d ∈ Icc 2 C, (C / d) ^ 2 := by
        refine h1.trans (h2.trans (le_of_eq (sum_congr rfl fun d _ => ?_)))
        rw [card_product, Nat.Ioc_filter_dvd_card_eq_div]; ring
      exact_mod_cast this
    refine h3.trans ?_
    calc ∑ d ∈ Icc 2 C, ((C / d : ℕ) : ℝ) ^ 2 ≤ ∑ d ∈ Icc 2 C, (C : ℝ) ^ 2 * (1 / (d : ℝ) ^ 2) := by
          refine sum_le_sum fun d hd => ?_
          have hd0 : (0 : ℝ) < d := by
            have := (mem_Icc.mp hd).1; exact_mod_cast (by omega : 0 < d)
          have : ((C / d : ℕ) : ℝ) ≤ (C : ℝ) / d := Nat.cast_div_le
          calc ((C / d : ℕ) : ℝ) ^ 2 ≤ ((C : ℝ) / d) ^ 2 := pow_le_pow_left₀ (by positivity) this 2
            _ = (C : ℝ) ^ 2 * (1 / (d : ℝ) ^ 2) := by field_simp
      _ = (C : ℝ) ^ 2 * ∑ d ∈ Icc 2 C, (1 : ℝ) / (d : ℝ) ^ 2 := by rw [mul_sum]
      _ ≤ (C : ℝ) ^ 2 * (3 / 4) := by gcongr; exact sum_inv_sq_le C
      _ = 3 / 4 * (C : ℝ) ^ 2 := by ring
  have hQ : (C : ℝ) ^ 2 ≤ 4 * Q.card := by
    have : ((Q.card + B.card : ℕ) : ℝ) = (C : ℝ) ^ 2 := by exact_mod_cast hQB
    push_cast at this
    linarith
  -- symmetry: `Q ⊆ P ∪ swap P`
  have hsym : Q ⊆ fareyPairs C ∪ (fareyPairs C).image Prod.swap := by
    intro p hp
    simp only [Q, s, mem_filter, mem_product, mem_Ioc] at hp
    obtain ⟨⟨⟨ha0, haC⟩, ⟨hc0, hcC⟩⟩, hcop⟩ := hp
    rcases le_total p.1 p.2 with h | h
    · refine mem_union_left _ ?_
      simp only [fareyPairs, mem_filter, mem_product, mem_Ioc]
      exact ⟨⟨⟨ha0, haC⟩, ⟨hc0, hcC⟩⟩, h, hcop⟩
    · refine mem_union_right _ (mem_image.mpr ⟨p.swap, ?_, Prod.swap_swap p⟩)
      simp only [fareyPairs, mem_filter, mem_product, mem_Ioc, Prod.fst_swap, Prod.snd_swap]
      exact ⟨⟨⟨hc0, hcC⟩, ⟨ha0, haC⟩⟩, h, hcop.symm⟩
  have hQP : Q.card ≤ 2 * (fareyPairs C).card := by
    refine (card_le_card hsym).trans ((card_union_le _ _).trans ?_)
    have := card_image_le (s := fareyPairs C) (f := Prod.swap)
    omega
  have : (Q.card : ℝ) ≤ 2 * (fareyPairs C).card := by exact_mod_cast hQP
  linarith

/-! ## Farey intervals -/

/-- The Farey interval `[a/c − 1/(2cC), a/c − 1/(4cC)]`. -/
def fareyJ (C : ℕ) (p : ℕ × ℕ) : Set ℝ :=
  Set.Icc ((p.1 : ℝ) / p.2 - 1 / (2 * p.2 * C)) ((p.1 : ℝ) / p.2 - 1 / (4 * p.2 * C))

lemma mem_fareyPairs {C : ℕ} {p : ℕ × ℕ} (hp : p ∈ fareyPairs C) :
    1 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ C ∧ Nat.Coprime p.1 p.2 := by
  simp only [fareyPairs, mem_filter, mem_product, mem_Ioc] at hp
  exact ⟨hp.1.1.1, hp.2.1, hp.1.2.2, hp.2.2⟩

/-- Scaled membership: `x ∈ J(a,c)` iff `aC − 1/2 ≤ x c C ≤ aC − 1/4`. -/
lemma fareyJ_scaled {C : ℕ} {p : ℕ × ℕ} (hC : 1 ≤ C) (hc : 1 ≤ p.2) {x : ℝ}
    (hx : x ∈ fareyJ C p) :
    (p.1 : ℝ) * C - 1 / 2 ≤ x * p.2 * C ∧ x * p.2 * C ≤ (p.1 : ℝ) * C - 1 / 4 := by
  have hc0 : (0 : ℝ) < p.2 := by exact_mod_cast hc
  have hC0 : (0 : ℝ) < C := by exact_mod_cast hC
  have hcC : (0 : ℝ) < p.2 * C := by positivity
  obtain ⟨h1, h2⟩ := hx
  have e1 : ((p.1 : ℝ) / p.2 - 1 / (2 * p.2 * C)) * (p.2 * C) = (p.1 : ℝ) * C - 1 / 2 := by
    field_simp
  have e2 : ((p.1 : ℝ) / p.2 - 1 / (4 * p.2 * C)) * (p.2 * C) = (p.1 : ℝ) * C - 1 / 4 := by
    field_simp
  have k1 := mul_le_mul_of_nonneg_right h1 hcC.le
  have k2 := mul_le_mul_of_nonneg_right h2 hcC.le
  rw [e1] at k1; rw [e2] at k2
  rw [mul_assoc]
  exact ⟨k1, k2⟩

lemma fareyJ_disjoint {C : ℕ} (hC : 1 ≤ C) :
    Set.Pairwise (↑(fareyPairs C) : Set (ℕ × ℕ)) (Function.onFun Disjoint (fareyJ C)) := by
  intro p hp q hq hpq
  rw [Function.onFun, Set.disjoint_left]
  intro x hxp hxq
  obtain ⟨ha, hac, hcC, hcop⟩ := mem_fareyPairs hp
  obtain ⟨ha', hac', hcC', hcop'⟩ := mem_fareyPairs hq
  obtain ⟨h1, h2⟩ := fareyJ_scaled hC (ha.trans hac) hxp
  obtain ⟨h1', h2'⟩ := fareyJ_scaled hC (ha'.trans hac') hxq
  have hc : (1 : ℝ) ≤ p.2 := by exact_mod_cast ha.trans hac
  have hc' : (1 : ℝ) ≤ q.2 := by exact_mod_cast ha'.trans hac'
  have hCc : (p.2 : ℝ) ≤ C := by exact_mod_cast hcC
  have hCc' : (q.2 : ℝ) ≤ C := by exact_mod_cast hcC'
  have hC0 : (0 : ℝ) < C := by exact_mod_cast hC
  -- `(a c' − a' c) C ∈ (−C/2, C/2)`
  set k : ℤ := (p.1 : ℤ) * q.2 - (q.1 : ℤ) * p.2
  have hk : (k : ℝ) = (p.1 : ℝ) * q.2 - (q.1 : ℝ) * p.2 := by simp [k]
  have hup : (k : ℝ) * C < C / 2 := by
    rw [hk]
    nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ q.2),
      mul_le_mul_of_nonneg_left h2' (by linarith : (0 : ℝ) ≤ p.2)]
  have hlo : -(C / 2 : ℝ) < (k : ℝ) * C := by
    rw [hk]
    nlinarith [mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ q.2),
      mul_le_mul_of_nonneg_left h1' (by linarith : (0 : ℝ) ≤ p.2)]
  have hk0 : k = 0 := by
    have h3 : (k : ℝ) < 1 := by
      by_contra h; push Not at h; nlinarith
    have h4 : (-1 : ℝ) < k := by
      by_contra h; push Not at h; nlinarith
    have h3' : k < 1 := by exact_mod_cast h3
    have h4' : -1 < k := by exact_mod_cast h4
    omega
  have heq : p.1 * q.2 = q.1 * p.2 := by
    have : (p.1 : ℤ) * q.2 = (q.1 : ℤ) * p.2 := by simp only [k] at hk0; linarith
    exact_mod_cast this
  -- coprimality forces `p = q`
  have hd1 : p.2 ∣ q.2 := by
    have : p.2 ∣ p.1 * q.2 := heq ▸ Dvd.intro_left _ rfl
    exact (Nat.Coprime.symm hcop).dvd_of_dvd_mul_left this
  have hd2 : q.2 ∣ p.2 := by
    have : q.2 ∣ q.1 * p.2 := heq.symm ▸ Dvd.intro_left _ rfl
    exact (Nat.Coprime.symm hcop').dvd_of_dvd_mul_left this
  have hc2 : p.2 = q.2 := Nat.dvd_antisymm hd1 hd2
  have hc1 : p.1 = q.1 := by
    rw [hc2] at heq
    exact Nat.eq_of_mul_eq_mul_right (by omega) heq
  exact hpq (Prod.ext hc1 hc2)

lemma fareyJ_subset {C : ℕ} (hC : 1 ≤ C) {p : ℕ × ℕ} (hp : p ∈ fareyPairs C) :
    fareyJ C p ⊆ Set.Ioc 0 1 := by
  obtain ⟨ha, hac, hcC, -⟩ := mem_fareyPairs hp
  intro x ⟨h1, h2⟩
  have hc : (1 : ℝ) ≤ p.2 := by exact_mod_cast ha.trans hac
  have hC1 : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have ha1 : (1 : ℝ) ≤ p.1 := by exact_mod_cast ha
  have hac1 : (p.1 : ℝ) ≤ p.2 := by exact_mod_cast hac
  have hc0 : (0 : ℝ) < p.2 := by linarith
  constructor
  · refine lt_of_lt_of_le ?_ h1
    have e1 : (1 : ℝ) / p.2 ≤ (p.1 : ℝ) / p.2 := by gcongr
    have e2 : (1 : ℝ) / (2 * p.2 * C) < 1 / p.2 := by
      rw [div_lt_div_iff₀ (by positivity) hc0]; nlinarith
    linarith
  · refine h2.trans ?_
    have e1 : (p.1 : ℝ) / p.2 ≤ 1 := by rw [div_le_one hc0]; exact hac1
    have e2 : (0 : ℝ) ≤ 1 / (4 * p.2 * C) := by positivity
    linarith

lemma volume_fareyJ {C : ℕ} (hC : 1 ≤ C) {p : ℕ × ℕ} (hp : p ∈ fareyPairs C) :
    volume.real (fareyJ C p) = 1 / (4 * p.2 * C) := by
  obtain ⟨ha, hac, -, -⟩ := mem_fareyPairs hp
  have hc : (0 : ℝ) < p.2 := by exact_mod_cast (by omega : 0 < p.2)
  have hC0 : (0 : ℝ) < C := by exact_mod_cast hC
  rw [fareyJ, Real.volume_real_Icc]
  rw [max_eq_left]
  · field_simp; ring
  · have : (1 : ℝ) / (4 * p.2 * C) ≤ 1 / (2 * p.2 * C) := by
      gcongr; linarith
    linarith

/-- **Farey lower bound for the horocycle integral.** -/
theorem integral_lower : ∃ m : ℝ, 0 < m ∧ ∀ (C : ℕ), 1 ≤ C → ∀ (hy : (0 : ℝ) < 1 / (C : ℝ) ^ 2),
    m / 32 * (C : ℝ) ^ 24 ≤ ∫ x in (0 : ℝ)..1, ‖Δf (hp hy x)‖ ^ 2 := by
  obtain ⟨m, hm0, hm⟩ := exists_band_lower
  refine ⟨m, hm0, fun C hC hy => ?_⟩
  set f : ℝ → ℝ := fun x => ‖Δf (hp hy x)‖ ^ 2
  have hC0 : (0 : ℝ) < C := by exact_mod_cast hC
  have hcont : Continuous f :=
    ((ModularFormClass.holo (CuspForm.discriminant : CuspForm 𝒮ℒ 12)).continuous.comp
      (continuous_hp hy)).norm.pow 2
  set P := fareyPairs C
  -- lower bound on each interval
  have hJ : ∀ p ∈ P, m * (C : ℝ) ^ 24 * (1 / (4 * p.2 * C)) ≤ ∫ x in fareyJ C p, f x := by
    intro p hp
    obtain ⟨ha, hac, hcC, hcop⟩ := mem_fareyPairs hp
    rw [← volume_fareyJ hC hp]
    refine setIntegral_ge_of_const_le_real measurableSet_Icc ?_ (fun x hx => ?_)
      hcont.integrableOn_Icc
    · rw [fareyJ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    · obtain ⟨h1, h2⟩ := hx
      exact normSq_farey_lower hm hC ha hac hcC hcop (by linarith) (by linarith) hy
  have hunion : ∫ x in ⋃ p ∈ P, fareyJ C p, f x = ∑ p ∈ P, ∫ x in fareyJ C p, f x :=
    integral_biUnion_finset P (fun p _ => measurableSet_Icc) (fareyJ_disjoint hC)
      (fun p _ => hcont.integrableOn_Icc)
  have hsub : (⋃ p ∈ P, fareyJ C p) ⊆ Set.Ioc 0 1 :=
    Set.iUnion₂_subset fun p hp => fareyJ_subset hC hp
  have hmono : ∫ x in ⋃ p ∈ P, fareyJ C p, f x ≤ ∫ x in Set.Ioc (0 : ℝ) 1, f x :=
    setIntegral_mono_set (hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
      (Filter.Eventually.of_forall fun x => by positivity) (Filter.Eventually.of_forall hsub)
  rw [intervalIntegral.integral_of_le zero_le_one]
  refine le_trans ?_ (hunion ▸ hmono)
  -- `∑_P m C²⁴/(4cC) ≥ #P · m C²⁴/(4C²) ≥ m C²⁴/32`
  have hterm : ∀ p ∈ P, m * (C : ℝ) ^ 24 * (1 / (4 * (C : ℝ) * C)) ≤
      m * (C : ℝ) ^ 24 * (1 / (4 * p.2 * C)) := by
    intro p hp
    obtain ⟨ha, hac, hcC, -⟩ := mem_fareyPairs hp
    have hc0 : (0 : ℝ) < p.2 := by exact_mod_cast (by omega : 0 < p.2)
    have : (p.2 : ℝ) ≤ C := by exact_mod_cast hcC
    gcongr
  have hcard := card_fareyPairs_ge C
  calc m / 32 * (C : ℝ) ^ 24
      ≤ P.card * (m * (C : ℝ) ^ 24 * (1 / (4 * (C : ℝ) * C))) := by
        rw [show m / 32 * (C : ℝ) ^ 24 = ((C : ℝ) ^ 2 / 8) * (m * (C : ℝ) ^ 24 *
          (1 / (4 * (C : ℝ) * C))) by field_simp; ring]
        gcongr
        linarith
    _ = ∑ p ∈ P, m * (C : ℝ) ^ 24 * (1 / (4 * (C : ℝ) * C)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ p ∈ P, m * (C : ℝ) ^ 24 * (1 / (4 * p.2 * C)) := sum_le_sum hterm
    _ ≤ ∑ p ∈ P, ∫ x in fareyJ C p, f x := sum_le_sum hJ

end RamanujanTau.RankinSelberg
