import RamanujanTau.TauDensity.NormFormDensity

/-! # Sharper: `#{n ≤ N : τ(n) ≠ 0} ≥ N / (585 103 (1 + log N))`

Refines the energy bound of `NormFormCount` by using all four constraints on the parametrisation
`(g,s,t,h)` of a coincidence: `gs ≤ 2A`, `th ≤ 2A`, `gt ≤ 691B`, `sh ≤ 2B`. For fixed `(s,t)` the number
of `(g,h)` is `≤ (2A/s)(2B/s)` if `t ≤ s` and `≤ (691B/t)(2A/t)` if `s ≤ t`, and
`∑_{s,t ≤ M} [t ≤ s]/s² = H_M`. So the off-diagonal energy is `≤ 1386·AB·(1 + log 2A)`, i.e. `O(N log N)`.
-/

set_option autoImplicit false

namespace RamanujanTau.TauDensity
open RamanujanTau Finset

/-- `∑_{s,t ∈ [1,M]} [t ≤ s]·X/s² ≤ X(1 + log M)`. -/
theorem tri_sum_le (M : ℕ) {X : ℝ} (hX : 0 ≤ X) :
    ∑ s ∈ Icc 1 M, ∑ t ∈ Icc 1 M, (if t ≤ s then X / (s : ℝ) ^ 2 else 0) ≤ X * (1 + Real.log M) := by
  have hin : ∀ s ∈ Icc 1 M, ∑ t ∈ Icc 1 M, (if t ≤ s then X / (s : ℝ) ^ 2 else 0) =
      X * (s : ℝ)⁻¹ := by
    intro s hs
    obtain ⟨hs1, hsM⟩ := mem_Icc.mp hs
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    have hf : (Icc 1 M).filter (fun t => t ≤ s) = Icc 1 s := by
      ext t; simp only [mem_filter, mem_Icc]; omega
    rw [hf, Nat.card_Icc, Nat.add_sub_cancel]
    have : (0 : ℝ) < s := by exact_mod_cast hs1
    field_simp
  rw [sum_congr rfl hin, ← mul_sum]
  have : ∑ s ∈ Icc 1 M, (s : ℝ)⁻¹ = (harmonic M : ℝ) := by
    rw [harmonic_eq_sum_Icc]; push_cast; rfl
  rw [this]
  gcongr
  exact harmonic_le_one_add_log M

/-- the refined target region -/
def quadBox (A B : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (hyp (2 * A) ×ˢ hyp (2 * A)).filter (fun q => q.1.1 * q.2.1 ≤ 691 * B ∧ q.1.2 * q.2.2 ≤ 2 * B)

theorem card_offdiag_le_quadBox (A B : ℕ) :
    ((box A B ×ˢ box A B).filter (fun pq => nf pq.1 = nf pq.2 ∧ pq.1.2 < pq.2.2)).card ≤
      (quadBox A B).card := by
  refine card_le_card_of_injOn phi (fun pq hpq => ?_) (fun pq hpq pq' hpq' heq => ?_)
  · obtain ⟨⟨x, y⟩, ⟨u, v⟩⟩ := pq
    simp only [coe_filter, Set.mem_setOf_eq, mem_product, box, mem_Icc, nf] at hpq
    obtain ⟨⟨⟨⟨hx1, hxA⟩, hy1, hyB⟩, ⟨hu1, huA⟩, hv1, hvB⟩, he, hyv⟩ := hpq
    obtain ⟨hux, hab⟩ := coincidence_facts he hyv
    obtain ⟨f1, f2, f3, f4⟩ := factor_facts (by omega) (by omega) hab
    simp only [phi, quadBox, coe_filter, hyp, mem_product, mem_filter, mem_Icc, Set.mem_setOf_eq]
    generalize (quad (x - u) (x + u) (v - y)).1.1 = g at f1 f2 f3 f4 ⊢
    generalize (quad (x - u) (x + u) (v - y)).1.2 = s at f1 f2 f3 f4 ⊢
    generalize (quad (x - u) (x + u) (v - y)).2.1 = t at f1 f2 f3 f4 ⊢
    generalize (quad (x - u) (x + u) (v - y)).2.2 = h at f1 f2 f3 f4 ⊢
    have hgs : 0 < g * s := by omega
    have hth : 0 < t * h := by omega
    have g1 : 1 ≤ g := Nat.pos_of_ne_zero (by rintro rfl; simp at hgs)
    have s1 : 1 ≤ s := Nat.pos_of_ne_zero (by rintro rfl; simp at hgs)
    have t1 : 1 ≤ t := Nat.pos_of_ne_zero (by rintro rfl; simp at hth)
    have h1 : 1 ≤ h := Nat.pos_of_ne_zero (by rintro rfl; simp at hth)
    have gs : g ≤ g * s := Nat.le_mul_of_pos_right _ s1
    have sg : s ≤ g * s := Nat.le_mul_of_pos_left _ g1
    have th : t ≤ t * h := Nat.le_mul_of_pos_right _ h1
    have ht : h ≤ t * h := Nat.le_mul_of_pos_left _ t1
    refine ⟨⟨⟨⟨⟨g1, ?_⟩, s1, ?_⟩, ?_⟩, ⟨⟨t1, ?_⟩, h1, ?_⟩, ?_⟩, ?_, ?_⟩ <;> omega
  · exact card_offdiag_le_injOn_aux hpq hpq' heq
where
  card_offdiag_le_injOn_aux {pq pq' : (ℕ × ℕ) × (ℕ × ℕ)}
      (hpq : pq ∈ ((box A B ×ˢ box A B).filter (fun pq => nf pq.1 = nf pq.2 ∧ pq.1.2 < pq.2.2) :
        Set ((ℕ × ℕ) × (ℕ × ℕ))))
      (hpq' : pq' ∈ ((box A B ×ˢ box A B).filter (fun pq => nf pq.1 = nf pq.2 ∧ pq.1.2 < pq.2.2) :
        Set ((ℕ × ℕ) × (ℕ × ℕ))))
      (heq : phi pq = phi pq') : pq = pq' := by
    obtain ⟨⟨x, y⟩, ⟨u, v⟩⟩ := pq
    obtain ⟨⟨x', y'⟩, ⟨u', v'⟩⟩ := pq'
    simp only [coe_filter, Set.mem_setOf_eq, mem_product, box, mem_Icc, nf] at hpq hpq'
    obtain ⟨-, he, hyv⟩ := hpq
    obtain ⟨-, he', hyv'⟩ := hpq'
    obtain ⟨hux, hab⟩ := coincidence_facts he hyv
    obtain ⟨hux', hab'⟩ := coincidence_facts he' hyv'
    obtain ⟨f1, f2, f3, f4⟩ := factor_facts (by omega) (by omega) hab
    obtain ⟨f1', f2', f3', f4'⟩ := factor_facts (by omega) (by omega) hab'
    simp only [phi] at heq
    rw [heq] at f1 f2 f3 f4
    have e1 : x - u = x' - u' := f1.symm.trans f1'
    have e2 : x + u = x' + u' := f2.symm.trans f2'
    have e3 : v - y = v' - y' := by have := f3.symm.trans f3'; omega
    have e4 : v + y = v' + y' := f4.symm.trans f4'
    simp only [Prod.mk.injEq]
    omega

theorem card_filter_le_div (M L s : ℕ) (hs : 1 ≤ s) (p : ℕ → Prop) [DecidablePred p]
    (hp : ∀ g, p g → g * s ≤ L) : (((Icc 1 M).filter p).card : ℝ) ≤ (L : ℝ) / s := by
  have hsub : (Icc 1 M).filter p ⊆ Icc 1 (L / s) := by
    intro g hg
    obtain ⟨hgI, hpg⟩ := mem_filter.mp hg
    exact mem_Icc.mpr ⟨(mem_Icc.mp hgI).1, (Nat.le_div_iff_mul_le (by omega)).mpr (hp g hpg)⟩
  have := card_le_card hsub
  rw [Nat.card_Icc, Nat.add_sub_cancel] at this
  exact (Nat.cast_le.mpr this).trans Nat.cast_div_le

/-- **Refined region count.** `#quadBox ≤ (MJ + KM)(1 + log M)` with `M = 2A`, `K = 691B`, `J = 2B`. -/
theorem card_quadBox_le (A B : ℕ) :
    ((quadBox A B).card : ℝ) ≤
      (((2 * A : ℕ) : ℝ) * ((2 * B : ℕ) : ℝ) + ((691 * B : ℕ) : ℝ) * ((2 * A : ℕ) : ℝ)) *
        (1 + Real.log ((2 * A : ℕ) : ℝ)) := by
  set M := 2 * A
  set K := 691 * B
  set J := 2 * B
  let G : ℕ × ℕ → Finset ℕ := fun st => (Icc 1 M).filter (fun g => g * st.1 ≤ M ∧ g * st.2 ≤ K)
  let Hh : ℕ × ℕ → Finset ℕ := fun st => (Icc 1 M).filter (fun h => st.2 * h ≤ M ∧ st.1 * h ≤ J)
  have hsub : quadBox A B ⊆ (Icc 1 M ×ˢ Icc 1 M).biUnion
      (fun st => (G st ×ˢ {st.1}) ×ˢ ({st.2} ×ˢ Hh st)) := by
    rintro ⟨⟨g, s⟩, ⟨t, h⟩⟩ hq
    simp only [quadBox, hyp, mem_filter, mem_product, mem_Icc] at hq
    obtain ⟨⟨⟨⟨hg, hs⟩, hgs⟩, ⟨ht, hh⟩, hth⟩, hgt, hsh⟩ := hq
    simp only [mem_biUnion, mem_product, mem_Icc, mem_singleton, G, Hh, mem_filter]
    exact ⟨(s, t), ⟨hs, ht⟩, ⟨⟨hg, hgs, hgt⟩, rfl⟩, rfl, hh, hth, hsh⟩
  have hcard := (card_le_card hsub).trans card_biUnion_le
  have hX1 : (0 : ℝ) ≤ (M : ℝ) * J := by positivity
  have hX2 : (0 : ℝ) ≤ (K : ℝ) * M := by positivity
  have hterm : ∀ st ∈ Icc 1 M ×ˢ Icc 1 M,
      ((((G st ×ˢ {st.1}) ×ˢ ({st.2} ×ˢ Hh st)).card : ℕ) : ℝ) ≤
        (if st.2 ≤ st.1 then (M : ℝ) * J / (st.1 : ℝ) ^ 2 else 0) +
        (if st.1 ≤ st.2 then (K : ℝ) * M / (st.2 : ℝ) ^ 2 else 0) := by
    rintro ⟨s, t⟩ hst
    obtain ⟨⟨hs1, -⟩, ht1, -⟩ := by simpa only [mem_product, mem_Icc] using hst
    simp only [card_product, card_singleton, mul_one, one_mul, Nat.cast_mul]
    have hG1 : ((G (s, t)).card : ℝ) ≤ (M : ℝ) / s :=
      card_filter_le_div M M s hs1 _ (fun g hg => hg.1)
    have hG2 : ((G (s, t)).card : ℝ) ≤ (K : ℝ) / t :=
      card_filter_le_div M K t ht1 _ (fun g hg => hg.2)
    have hH1 : ((Hh (s, t)).card : ℝ) ≤ (J : ℝ) / s :=
      card_filter_le_div M J s hs1 _ (fun h hh => by simpa [mul_comm] using hh.2)
    have hH2 : ((Hh (s, t)).card : ℝ) ≤ (M : ℝ) / t :=
      card_filter_le_div M M t ht1 _ (fun h hh => by simpa [mul_comm] using hh.1)
    have hs0 : (0 : ℝ) < s := by exact_mod_cast hs1
    have ht0 : (0 : ℝ) < t := by exact_mod_cast ht1
    have c0 : (0 : ℝ) ≤ (G (s, t)).card := Nat.cast_nonneg _
    have d0 : (0 : ℝ) ≤ (Hh (s, t)).card := Nat.cast_nonneg _
    by_cases hts : t ≤ s
    · rw [if_pos hts]
      have : ((G (s, t)).card : ℝ) * (Hh (s, t)).card ≤ (M : ℝ) / s * ((J : ℝ) / s) :=
        mul_le_mul hG1 hH1 d0 (by positivity)
      have e : (M : ℝ) / s * ((J : ℝ) / s) = (M : ℝ) * J / (s : ℝ) ^ 2 := by ring
      have : (0 : ℝ) ≤ (if s ≤ t then (K : ℝ) * M / (t : ℝ) ^ 2 else 0) := by
        split_ifs <;> positivity
      linarith
    · rw [if_neg hts, if_pos (by omega)]
      have : ((G (s, t)).card : ℝ) * (Hh (s, t)).card ≤ (K : ℝ) / t * ((M : ℝ) / t) :=
        mul_le_mul hG2 hH2 d0 (by positivity)
      have e : (K : ℝ) / t * ((M : ℝ) / t) = (K : ℝ) * M / (t : ℝ) ^ 2 := by ring
      linarith
  have hsum := sum_le_sum hterm
  rw [sum_add_distrib] at hsum
  have t1 : ∑ st ∈ Icc 1 M ×ˢ Icc 1 M,
      (if st.2 ≤ st.1 then (M : ℝ) * J / (st.1 : ℝ) ^ 2 else 0) ≤ (M : ℝ) * J * (1 + Real.log M) := by
    rw [sum_product]; exact tri_sum_le M hX1
  have t2 : ∑ st ∈ Icc 1 M ×ˢ Icc 1 M,
      (if st.1 ≤ st.2 then (K : ℝ) * M / (st.2 : ℝ) ^ 2 else 0) ≤ (K : ℝ) * M * (1 + Real.log M) := by
    rw [sum_product, sum_comm]; exact tri_sum_le M hX2
  calc ((quadBox A B).card : ℝ)
      ≤ ((∑ st ∈ Icc 1 M ×ˢ Icc 1 M, ((G st ×ˢ {st.1}) ×ˢ ({st.2} ×ˢ Hh st)).card : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ ≤ (M : ℝ) * J * (1 + Real.log M) + (K : ℝ) * M * (1 + Real.log M) := by
        push_cast; linarith
    _ = _ := by ring

/-- **Sharper headline.** For every `N`, `N / (585 103 (1 + log N)) ≤ #{n ∈ [1,N] : τ(n) ≠ 0}`. -/
theorem card_tau_ne_zero_ge_div_log_of_le {N : ℕ} (hN : 1382 ≤ N) :
    (N : ℝ) / (585103 * (1 + Real.log N)) ≤
      (((Icc 1 N).filter (fun n => τ n ≠ 0)).card : ℝ) := by
  set A := Nat.sqrt (N / 2) with hAdef
  set B := Nat.sqrt (N / 1382) with hBdef
  set Z := ((Icc 1 N).filter (fun n => τ n ≠ 0)).card
  set I := ((box A B).image nf).card
  set E := ((box A B ×ˢ box A B).filter (fun pq => nf pq.1 = nf pq.2)).card
  set E1 := ((box A B ×ˢ box A B).filter (fun pq => nf pq.1 = nf pq.2 ∧ pq.1.2 < pq.2.2)).card
  have hA2 : A ^ 2 ≤ N / 2 := Nat.sqrt_le' _
  have hB2 : B ^ 2 ≤ N / 1382 := Nat.sqrt_le' _
  have hA1 : 1 ≤ A := Nat.le_sqrt.mpr (by omega)
  have hB1 : 1 ≤ B := Nat.le_sqrt.mpr (by omega)
  have hAl : N / 2 < (A + 1) ^ 2 := Nat.lt_succ_sqrt' _
  have hBl : N / 1382 < (B + 1) ^ 2 := Nat.lt_succ_sqrt' _
  have hNA : N ≤ 8 * A ^ 2 := by
    have := Nat.div_add_mod N 2; have := Nat.mod_lt N (show 2 > 0 by omega); nlinarith
  have hNB : N ≤ 5528 * B ^ 2 := by
    have := Nat.div_add_mod N 1382; have := Nat.mod_lt N (show 1382 > 0 by omega); nlinarith
  have hA2N : 2 * A ^ 2 ≤ N := by have := Nat.div_mul_le_self N 2; omega
  have hIZ : I ≤ Z := by
    refine card_le_card fun n hn => ?_
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := mem_image.mp hn
    simp only [box, mem_product, mem_Icc] at hxy
    obtain ⟨⟨hx1, hxA⟩, hy1, hyB⟩ := hxy
    have hB2N : 1382 * B ^ 2 ≤ N := by have := Nat.div_mul_le_self N 1382; omega
    have hx2 : x ^ 2 ≤ A ^ 2 := Nat.pow_le_pow_left hxA 2
    have hy2 : y ^ 2 ≤ B ^ 2 := Nat.pow_le_pow_left hyB 2
    have hx0 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ hx1
    simp only [nf, mem_filter, mem_Icc]
    exact ⟨⟨by omega, by omega⟩, tau_norm_form_ne_zero (by omega)⟩
  have hCS : (A * B) ^ 2 ≤ I * E := by
    have := card_sq_le_card_image_mul_energy (box A B) nf
    simpa [box, card_product] using this
  -- energy split (as in `card_energy_le`)
  have hE : E ≤ A * B + 2 * E1 := by
    have hsub : (box A B ×ˢ box A B).filter (fun pq => nf pq.1 = nf pq.2) ⊆
        ((box A B).image (fun p => (p, p)) ∪
          (box A B ×ˢ box A B).filter (fun pq => nf pq.1 = nf pq.2 ∧ pq.1.2 < pq.2.2)) ∪
          ((box A B ×ˢ box A B).filter (fun pq => nf pq.1 = nf pq.2 ∧ pq.1.2 < pq.2.2)).image
            Prod.swap := by
      rintro ⟨⟨x, y⟩, ⟨u, v⟩⟩ hpq
      have hpq' := hpq
      simp only [mem_filter, mem_product, nf] at hpq'
      obtain ⟨⟨hp, hq⟩, he⟩ := hpq'
      simp only [mem_union, mem_image]
      rcases lt_trichotomy y v with hyv | rfl | hvy
      · left; right
        simp only [mem_filter, mem_product, nf]; exact ⟨⟨hp, hq⟩, he, hyv⟩
      · left; left
        have hxu : x = u := Nat.pow_left_injective two_ne_zero (by simpa using he)
        subst hxu
        exact ⟨(x, y), hp, rfl⟩
      · right
        refine ⟨((u, v), (x, y)), ?_, rfl⟩
        simp only [mem_filter, mem_product, nf]; exact ⟨⟨hq, hp⟩, he.symm, hvy⟩
    have h1 := (card_le_card hsub).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le _ _) _))
    have i1 : ((box A B).image (fun p => (p, p))).card ≤ A * B :=
      card_image_le.trans (by simp [box, card_product])
    have i2 : (((box A B ×ˢ box A B).filter
        (fun pq => nf pq.1 = nf pq.2 ∧ pq.1.2 < pq.2.2)).image Prod.swap).card ≤ E1 := card_image_le
    omega
  have hE1 : (E1 : ℝ) ≤ 1386 * ((A * B : ℕ) : ℝ) * (1 + Real.log N) := by
    have q1 : (E1 : ℝ) ≤ (quadBox A B).card := by exact_mod_cast card_offdiag_le_quadBox A B
    have q2 := card_quadBox_le A B
    have hM1 : (1 : ℝ) ≤ ((2 * A : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 2 * A by omega)
    have hMN : ((2 * A : ℕ) : ℝ) ≤ N := by
      have : 2 * A ≤ N := by nlinarith
      exact_mod_cast this
    have hlogM : Real.log ((2 * A : ℕ) : ℝ) ≤ Real.log N := Real.log_le_log (by linarith) hMN
    have hlogM0 : 0 ≤ Real.log ((2 * A : ℕ) : ℝ) := Real.log_nonneg hM1
    have e : ((2 * A : ℕ) : ℝ) * ((2 * B : ℕ) : ℝ) + ((691 * B : ℕ) : ℝ) * ((2 * A : ℕ) : ℝ) =
        1386 * ((A * B : ℕ) : ℝ) := by push_cast; ring
    rw [e] at q2
    have hAB0 : (0 : ℝ) ≤ ((A * B : ℕ) : ℝ) := Nat.cast_nonneg _
    have : 1386 * ((A * B : ℕ) : ℝ) * (1 + Real.log ((2 * A : ℕ) : ℝ)) ≤
        1386 * ((A * B : ℕ) : ℝ) * (1 + Real.log N) := by gcongr
    linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  set L := Real.log N
  set P : ℝ := ((A * B : ℕ) : ℝ)
  have hP0 : 0 < P := by
    have : 0 < A * B := Nat.mul_pos (by omega) (by omega)
    simp only [P]; exact_mod_cast this
  have hER : (E : ℝ) ≤ 2773 * P * (1 + L) := by
    have : (E : ℝ) ≤ P + 2 * E1 := by simp only [P]; exact_mod_cast hE
    nlinarith
  have hlow : (N : ℝ) ≤ 211 * P := by
    have : N ≤ 211 * (A * B) := by
      have h := Nat.mul_le_mul hNA hNB
      have h2 : N * N ≤ (211 * (A * B)) * (211 * (A * B)) := by nlinarith
      exact Nat.mul_self_le_mul_self_iff.mp h2
    simp only [P]; exact_mod_cast this
  have hCSR : P ^ 2 ≤ (I : ℝ) * E := by simp only [P]; exact_mod_cast hCS
  have hIZR : (I : ℝ) ≤ Z := by exact_mod_cast hIZ
  have hI0 : (0 : ℝ) ≤ I := Nat.cast_nonneg _
  have key : P * P ≤ P * (2773 * (1 + L) * Z) := by
    have h1 : (I : ℝ) * E ≤ I * (2773 * P * (1 + L)) := mul_le_mul_of_nonneg_left hER hI0
    have h2 : (I : ℝ) * (2773 * P * (1 + L)) ≤ Z * (2773 * P * (1 + L)) :=
      mul_le_mul_of_nonneg_right hIZR (by positivity)
    calc P * P = P ^ 2 := (sq _).symm
      _ ≤ (I : ℝ) * E := hCSR
      _ ≤ Z * (2773 * P * (1 + L)) := h1.trans h2
      _ = P * (2773 * (1 + L) * Z) := by ring
  have hPZ : P ≤ 2773 * (1 + L) * Z := le_of_mul_le_mul_left key hP0
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- **Sharper headline (all `N`).** `N / (585 103 (1 + log N)) ≤ #{n ∈ [1,N] : τ(n) ≠ 0}`. -/
theorem card_tau_ne_zero_ge_div_log (N : ℕ) :
    (N : ℝ) / (585103 * (1 + Real.log N)) ≤
      (((Icc 1 N).filter (fun n => τ n ≠ 0)).card : ℝ) := by
  rcases Nat.lt_or_ge N 1382 with hN | hN
  · have h1 : min N 21492863998 = N := min_eq_left (by omega)
    have h2 := (le_max_right _ _).trans (card_tau_ne_zero_ge N)
    rw [h1] at h2
    have h2' : (N : ℝ) ≤ (((Icc 1 N).filter (fun n => τ n ≠ 0)).card : ℝ) := by exact_mod_cast h2
    rcases Nat.eq_zero_or_pos N with rfl | hpos
    · simp
    have hL0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hpos)
    refine le_trans ?_ h2'
    rw [div_le_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    nlinarith
  · exact card_tau_ne_zero_ge_div_log_of_le hN

end RamanujanTau.TauDensity

#print axioms RamanujanTau.TauDensity.tri_sum_le
#print axioms RamanujanTau.TauDensity.card_offdiag_le_quadBox
#print axioms RamanujanTau.TauDensity.card_quadBox_le
#print axioms RamanujanTau.TauDensity.card_tau_ne_zero_ge_div_log
