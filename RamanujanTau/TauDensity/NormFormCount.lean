import RamanujanTau.TauDensity.NormForm
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.Order.Chebyshev

/-! # Counting values of `x² + 691y²`: Cauchy–Schwarz + an energy bound

* `card_sq_le_card_image_mul_energy`: `|s|² ≤ |f(s)| · #{(p,q) ∈ s² : f p = f q}`.
* `factor_facts`: `ab = 691cd` (all positive) gives `(g,s,t,h)` with `a = gs`, `b = th`, `691c = gt`, `d = sh`.
* `card_energy_le`: on `P = [1,A] × [1,B]`, `#{(p,q) ∈ P² : x²+691y² = u²+691v²} ≤ AB + 2·#S²`
  with `S = {(g,s) ∈ [1,2A]² : gs ≤ 2A}`.
* `card_hyperbola_le`: `#S ≤ M(1 + log M)` for `M = 2A`.
-/

set_option autoImplicit false

namespace RamanujanTau.TauDensity
open RamanujanTau Finset

/-- **Cauchy–Schwarz for images.** -/
theorem card_sq_le_card_image_mul_energy {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β) :
    s.card ^ 2 ≤ (s.image f).card * ((s ×ˢ s).filter (fun pq => f pq.1 = f pq.2)).card := by
  have h1 : s.card = ∑ b ∈ s.image f, (s.filter (fun a => f a = b)).card :=
    card_eq_sum_card_image f s
  have h2 : ((s ×ˢ s).filter (fun pq => f pq.1 = f pq.2)).card =
      ∑ b ∈ s.image f, (s.filter (fun a => f a = b)).card ^ 2 := by
    rw [card_eq_sum_card_fiberwise (f := fun pq => f pq.1) (t := s.image f)]
    · refine sum_congr rfl fun b _ => ?_
      rw [sq, ← card_product]
      congr 1
      ext ⟨p, q⟩
      simp only [mem_filter, mem_product]
      constructor
      · rintro ⟨⟨⟨hp, hq⟩, he⟩, hb⟩; exact ⟨⟨hp, hb⟩, hq, he.symm.trans hb⟩
      · rintro ⟨⟨hp, hb⟩, hq, hb'⟩; exact ⟨⟨⟨hp, hq⟩, hb.trans hb'.symm⟩, hb⟩
    · intro pq hpq
      rw [mem_coe, mem_filter, mem_product] at hpq
      exact mem_coe.mpr (mem_image_of_mem f hpq.1.1)
  rw [h1, h2]
  exact sq_sum_le_card_mul_sum_sq

/-- The parametrisation of `ab = 691cd`: `g = gcd(a, 691c)`, `s = a/g`, `t = 691c/g`, `h = b/t`. -/
def quad (a b c : ℕ) : (ℕ × ℕ) × (ℕ × ℕ) :=
  ((Nat.gcd a (691 * c), a / Nat.gcd a (691 * c)),
    (691 * c / Nat.gcd a (691 * c), b / (691 * c / Nat.gcd a (691 * c))))

theorem factor_facts {a b c d : ℕ} (ha : 0 < a) (hc : 0 < c) (h : a * b = 691 * c * d) :
    (quad a b c).1.1 * (quad a b c).1.2 = a ∧ (quad a b c).2.1 * (quad a b c).2.2 = b ∧
      (quad a b c).1.1 * (quad a b c).2.1 = 691 * c ∧ (quad a b c).1.2 * (quad a b c).2.2 = d := by
  simp only [quad]
  set g := Nat.gcd a (691 * c)
  set s := a / g
  set t := 691 * c / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ ha
  have e1 : g * s = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have e3 : g * t = 691 * c := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
  have cop : Nat.Coprime s t := Nat.coprime_div_gcd_div_gcd hg
  have e : s * b = t * d := by
    apply Nat.eq_of_mul_eq_mul_left hg
    calc g * (s * b) = (g * s) * b := by ring
      _ = 691 * c * d := by rw [e1, h]
      _ = g * (t * d) := by rw [← e3]; ring
  have tdvd : t ∣ b := cop.symm.dvd_of_dvd_mul_left ⟨d, e⟩
  have e2 : t * (b / t) = b := Nat.mul_div_cancel' tdvd
  have tpos : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · rw [h0, mul_zero] at e3; omega
    · exact h0
  refine ⟨e1, e2, e3, ?_⟩
  apply Nat.eq_of_mul_eq_mul_left tpos
  calc t * (s * (b / t)) = s * (t * (b / t)) := by ring
    _ = t * d := by rw [e2, e]

/-- the norm form -/
def nf (p : ℕ × ℕ) : ℕ := p.1 ^ 2 + 691 * p.2 ^ 2

/-- the hyperbola region `{(g,s) ∈ [1,M]² : gs ≤ M}` -/
def hyp (M : ℕ) : Finset (ℕ × ℕ) := (Icc 1 M ×ˢ Icc 1 M).filter (fun gs => gs.1 * gs.2 ≤ M)

/-- the box `[1,A] × [1,B]` -/
def box (A B : ℕ) : Finset (ℕ × ℕ) := Icc 1 A ×ˢ Icc 1 B

/-- the map from off-diagonal coincidences (with `y < v`) to `hyp M × hyp M` -/
def phi (pq : (ℕ × ℕ) × (ℕ × ℕ)) : (ℕ × ℕ) × (ℕ × ℕ) :=
  quad (pq.1.1 - pq.2.1) (pq.1.1 + pq.2.1) (pq.2.2 - pq.1.2)

/-- algebra of a coincidence `x² + 691y² = u² + 691v²`, `y < v` -/
theorem coincidence_facts {x y u v : ℕ} (he : x ^ 2 + 691 * y ^ 2 = u ^ 2 + 691 * v ^ 2)
    (hyv : y < v) :
    u < x ∧ (x - u) * (x + u) = 691 * (v - y) * (v + y) := by
  obtain ⟨c, rfl⟩ : ∃ c, v = y + c := ⟨v - y, by omega⟩
  have hc : 0 < c := by omega
  have hux : u < x := by
    by_contra hh
    push Not at hh
    have : x ^ 2 ≤ u ^ 2 := Nat.pow_le_pow_left hh 2
    nlinarith
  refine ⟨hux, ?_⟩
  obtain ⟨a, rfl⟩ : ∃ a, x = u + a := ⟨x - u, by omega⟩
  rw [show u + a - u = a by omega, show y + c - y = c by omega]
  nlinarith

theorem card_offdiag_le (A B : ℕ) :
    ((box A B ×ˢ box A B).filter (fun pq => nf pq.1 = nf pq.2 ∧ pq.1.2 < pq.2.2)).card ≤
      (hyp (2 * A)).card ^ 2 := by
  rw [sq, ← card_product]
  refine card_le_card_of_injOn phi (fun pq hpq => ?_) (fun pq hpq pq' hpq' heq => ?_)
  · obtain ⟨⟨x, y⟩, ⟨u, v⟩⟩ := pq
    simp only [coe_filter, Set.mem_setOf_eq, mem_product, box, mem_Icc, nf] at hpq
    obtain ⟨⟨⟨⟨hx1, hxA⟩, hy1, hyB⟩, ⟨hu1, huA⟩, hv1, hvB⟩, he, hyv⟩ := hpq
    obtain ⟨hux, hab⟩ := coincidence_facts he hyv
    obtain ⟨f1, f2, -, -⟩ := factor_facts (by omega) (by omega) hab
    simp only [phi, coe_product, Set.mem_prod, hyp, coe_filter, mem_product, mem_Icc,
      Set.mem_setOf_eq]
    generalize (quad (x - u) (x + u) (v - y)).1.1 = g at f1 f2 ⊢
    generalize (quad (x - u) (x + u) (v - y)).1.2 = s at f1 f2 ⊢
    generalize (quad (x - u) (x + u) (v - y)).2.1 = t at f1 f2 ⊢
    generalize (quad (x - u) (x + u) (v - y)).2.2 = h at f1 f2 ⊢
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
    refine ⟨⟨⟨⟨g1, ?_⟩, s1, ?_⟩, ?_⟩, ⟨⟨t1, ?_⟩, h1, ?_⟩, ?_⟩ <;> omega
  · obtain ⟨⟨x, y⟩, ⟨u, v⟩⟩ := pq
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

/-- **Energy bound.** `#{(p,q) ∈ P² : nf p = nf q} ≤ AB + 2·#hyp(2A)²` on `P = [1,A] × [1,B]`. -/
theorem card_energy_le (A B : ℕ) :
    ((box A B ×ˢ box A B).filter (fun pq => nf pq.1 = nf pq.2)).card ≤
      A * B + 2 * (hyp (2 * A)).card ^ 2 := by
  set E1 := (box A B ×ˢ box A B).filter (fun pq => nf pq.1 = nf pq.2 ∧ pq.1.2 < pq.2.2)
  have hsub : (box A B ×ˢ box A B).filter (fun pq => nf pq.1 = nf pq.2) ⊆
      ((box A B).image (fun p => (p, p)) ∪ E1) ∪ E1.image Prod.swap := by
    rintro ⟨⟨x, y⟩, ⟨u, v⟩⟩ hpq
    have hpq' := hpq
    simp only [mem_filter, mem_product, nf] at hpq'
    obtain ⟨⟨hp, hq⟩, he⟩ := hpq'
    simp only [mem_union, mem_image]
    rcases lt_trichotomy y v with hyv | rfl | hvy
    · left; right
      simp only [E1, mem_filter, mem_product, nf]; exact ⟨⟨hp, hq⟩, he, hyv⟩
    · left; left
      have hxu : x = u := Nat.pow_left_injective two_ne_zero (by simpa using he)
      subst hxu
      exact ⟨(x, y), hp, rfl⟩
    · right
      refine ⟨((u, v), (x, y)), ?_, rfl⟩
      simp only [E1, mem_filter, mem_product, nf]; exact ⟨⟨hq, hp⟩, he.symm, hvy⟩
  have hbox : (box A B).card = A * B := by simp [box, card_product]
  calc ((box A B ×ˢ box A B).filter (fun pq => nf pq.1 = nf pq.2)).card
      ≤ (((box A B).image (fun p => (p, p)) ∪ E1) ∪ E1.image Prod.swap).card := card_le_card hsub
    _ ≤ ((box A B).image (fun p => (p, p))).card + E1.card + (E1.image Prod.swap).card := by
        refine (card_union_le _ _).trans ?_
        gcongr
        exact card_union_le _ _
    _ ≤ A * B + E1.card + E1.card := by
        have i1 : ((box A B).image (fun p => (p, p))).card ≤ A * B := card_image_le.trans hbox.le
        have i2 : (E1.image Prod.swap).card ≤ E1.card := card_image_le
        omega
    _ ≤ A * B + 2 * (hyp (2 * A)).card ^ 2 := by
        have : E1.card ≤ (hyp (2 * A)).card ^ 2 := card_offdiag_le A B
        omega

/-- **Hyperbola count.** `#{(g,s) ∈ [1,M]² : gs ≤ M} ≤ M(1 + log M)`. -/
theorem card_hyp_le (M : ℕ) : ((hyp M).card : ℝ) ≤ M * (1 + Real.log M) := by
  have hsub : hyp M ⊆ (Icc 1 M).biUnion (fun s => Icc 1 (M / s) ×ˢ {s}) := by
    rintro ⟨g, s⟩ h
    simp only [hyp, mem_filter, mem_product, mem_Icc] at h
    obtain ⟨⟨⟨hg1, -⟩, hs1, hsM⟩, hgs⟩ := h
    simp only [mem_biUnion, mem_product, mem_Icc, mem_singleton]
    exact ⟨s, ⟨hs1, hsM⟩, ⟨hg1, (Nat.le_div_iff_mul_le (by omega)).mpr hgs⟩, rfl⟩
  have hcard := (card_le_card hsub).trans card_biUnion_le
  have hterm : ∀ s ∈ Icc 1 M, (((Icc 1 (M / s) ×ˢ ({s} : Finset ℕ)).card : ℕ) : ℝ) ≤
      (M : ℝ) * (s : ℝ)⁻¹ := by
    intro s hs
    have hs1 : 1 ≤ s := (mem_Icc.mp hs).1
    rw [card_product, card_singleton, mul_one, Nat.card_Icc, Nat.add_sub_cancel]
    calc ((M / s : ℕ) : ℝ) ≤ (M : ℝ) / s := Nat.cast_div_le
      _ = (M : ℝ) * (s : ℝ)⁻¹ := div_eq_mul_inv _ _
  calc ((hyp M).card : ℝ) ≤ ((∑ s ∈ Icc 1 M, (Icc 1 (M / s) ×ˢ ({s} : Finset ℕ)).card : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ ≤ ∑ s ∈ Icc 1 M, (M : ℝ) * (s : ℝ)⁻¹ := by push_cast; exact sum_le_sum hterm
    _ = (M : ℝ) * (harmonic M : ℝ) := by rw [← mul_sum, harmonic_eq_sum_Icc]; push_cast; rfl
    _ ≤ (M : ℝ) * (1 + Real.log M) := by gcongr; exact harmonic_le_one_add_log M

end RamanujanTau.TauDensity
