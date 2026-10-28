/-
# Vélu kernels from chord data

`TorsData A B p`: points `P_k = (X k, Y k)` (`1 ≤ k < p`) on `y² = x³ + Ax + B`, with `Y k ≠ 0`,
the symmetry `P_{p−k} = −P_k`, distinct `x`-coordinates and the chord law `P_a + P_b = P_{a+b}` for
`1 ≤ a < b`, `a + b < p`. For `p ≥ 5` prime, `k ↦ P_k` (`P_0 = O`) is then a homomorphism
`ZMod p → E(L)` (`f_add`; doubling via `P_a = P_{2a} + P_{−a}`), and its image is a Vélu kernel
(`TorsData.kernel`) of order `p`, with representatives `S = {P_1, …, P_{(p−1)/2}}`, whose `A'`, `B'`
are `veluA A (Icc 1 (p/2)) X`, `veluB A B (Icc 1 (p/2)) X Y`.
-/
import RamanujanTau.TateQuot.Link

set_option autoImplicit false

noncomputable section

namespace TateAdd

open Velu WeierstrassCurve Finset

variable {L : Type*} [Field L] [DecidableEq L] {A B : L} {p : ℕ}

/-- chord data for the cyclic subgroup. -/
structure TorsData (A B : L) (p : ℕ) where
  X : ℕ → L
  Y : ℕ → L
  on : ∀ k, 1 ≤ k → k < p → Y k ^ 2 = X k ^ 3 + A * X k + B
  Yne : ∀ k, 1 ≤ k → k < p → Y k ≠ 0
  symX : ∀ k, 1 ≤ k → k < p → X (p - k) = X k
  symY : ∀ k, 1 ≤ k → k < p → Y (p - k) = -Y k
  dist : ∀ a b, 1 ≤ a → a < b → a + b < p → X a ≠ X b
  chord : ∀ a b, 1 ≤ a → a < b → a + b < p →
    X (a + b) = ((Y a - Y b) / (X a - X b)) ^ 2 - X a - X b ∧
      Y (a + b) = -((Y a - Y b) / (X a - X b) * (X (a + b) - X a) + Y a)

namespace TorsData

variable [CharZero L] (d : TorsData A B p)

lemma ns {k : ℕ} (h1 : 1 ≤ k) (h2 : k < p) : (short A B).Nonsingular (d.X k) (d.Y k) := by
  rw [Affine.nonsingular_iff, short_equation_iff]
  refine ⟨d.on k h1 h2, Or.inr ?_⟩
  simp only [short_a₁, short_a₃, zero_mul, sub_zero]
  intro h
  have : 2 * d.Y k = 0 := by linear_combination h
  exact d.Yne k h1 h2 ((mul_eq_zero.mp this).resolve_left two_ne_zero)

/-- `P_k` (`O` outside `1 ≤ k < p`). -/
def pt (k : ℕ) : (short A B).Point :=
  if h : 1 ≤ k ∧ k < p then .some (d.X k) (d.Y k) (d.ns h.1 h.2) else 0

lemma pt_of {k : ℕ} (h1 : 1 ≤ k) (h2 : k < p) : d.pt k = .some (d.X k) (d.Y k) (d.ns h1 h2) := by
  rw [pt, dif_pos ⟨h1, h2⟩]

lemma pt_zero : d.pt 0 = 0 := by rw [pt, dif_neg (by omega)]

lemma pt_ne {k : ℕ} (h1 : 1 ≤ k) (h2 : k < p) : d.pt k ≠ 0 := by
  rw [d.pt_of h1 h2]; exact Affine.Point.some_ne_zero _

lemma xc_pt {k : ℕ} (h1 : 1 ≤ k) (h2 : k < p) : xc (d.pt k) = d.X k := by rw [d.pt_of h1 h2]; rfl
lemma yc_pt {k : ℕ} (h1 : 1 ≤ k) (h2 : k < p) : yc (d.pt k) = d.Y k := by rw [d.pt_of h1 h2]; rfl

lemma some_congr {x y x' y' : L} (hx : x = x') (hy : y = y') (h : (short A B).Nonsingular x y)
    (h' : (short A B).Nonsingular x' y') : (Affine.Point.some x y h : (short A B).Point) =
      .some x' y' h' := by
  subst hx hy; rfl

lemma neg_pt {k : ℕ} (h1 : 1 ≤ k) (h2 : k < p) : -d.pt k = d.pt (p - k) := by
  rw [d.pt_of h1 h2, d.pt_of (by omega) (by omega), Affine.Point.neg_some]
  apply some_congr
  · exact (d.symX k h1 h2).symm
  · rw [d.symY k h1 h2]; simp [Affine.negY]

lemma eq_of_coords {P Q : (short A B).Point} (hP : P ≠ 0) (hQ : Q ≠ 0) (hx : xc P = xc Q)
    (hy : yc P = yc Q) : P = Q := by
  obtain ⟨h1, e1⟩ := eq_some_of_ne_zero hP
  obtain ⟨h2, e2⟩ := eq_some_of_ne_zero hQ
  rw [e1, e2]; exact some_congr hx hy _ _

/-- chord step. -/
lemma pt_add_chord {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) (hp : a + b < p) :
    d.pt a + d.pt b = d.pt (a + b) := by
  have hb1 : 1 ≤ b := by omega
  have hbp : b < p := by omega
  have hX : xc (d.pt a) ≠ xc (d.pt b) := by
    rw [d.xc_pt ha (by omega), d.xc_pt hb1 hbp]; exact d.dist a b ha hab hp
  obtain ⟨hx, hy⟩ := add_coords_of_xc_ne (d.pt_ne ha (by omega)) (d.pt_ne hb1 hbp) hX
  have hne : d.pt a + d.pt b ≠ 0 := by
    intro h0
    have := congrArg xc (neg_eq_of_add_eq_zero_right h0)
    rw [xc_neg] at this; exact hX this
  obtain ⟨hc1, hc2⟩ := d.chord a b ha hab hp
  refine eq_of_coords hne (d.pt_ne (by omega) hp) ?_ ?_
  · rw [hx, d.xc_pt (by omega) hp, hc1, d.xc_pt ha (by omega), d.xc_pt hb1 hbp,
      d.yc_pt ha (by omega), d.yc_pt hb1 hbp]
  · rw [hy, hx, d.yc_pt (by omega) hp, hc2, hc1, d.xc_pt ha (by omega), d.xc_pt hb1 hbp,
      d.yc_pt ha (by omega), d.yc_pt hb1 hbp]

/-- general chord: `a ≠ b`, `a + b ≠ p`. -/
lemma pt_add_ne {a b : ℕ} (ha : 1 ≤ a) (hap : a < p) (hb : 1 ≤ b) (hbp : b < p) (hab : a ≠ b)
    (hs : a + b ≠ p) : d.pt a + d.pt b = d.pt ((a + b) % p) := by
  wlog h : a < b generalizing a b
  · rw [add_comm, add_comm a b]; exact this hb hbp ha hap (Ne.symm hab) (by omega) (by omega)
  rcases Nat.lt_or_gt_of_ne hs with hlt | hgt
  · rw [Nat.mod_eq_of_lt hlt]; exact d.pt_add_chord ha h hlt
  · have e1 := d.neg_pt ha hap
    have e2 := d.neg_pt hb hbp
    have hc := d.pt_add_chord (a := p - b) (b := p - a) (by omega) (by omega) (by omega)
    have hm : (a + b) % p = a + b - p := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hm]
    have e3 := d.neg_pt (k := p - b + (p - a)) (by omega) (by omega)
    rw [show p - (p - b + (p - a)) = a + b - p by omega] at e3
    rw [← e3, ← hc, ← e1, ← e2, neg_add, add_comm]
    simp

/-! ### The homomorphism `ZMod p → E` -/

/-- `r ↦ P_{r.val}`. -/
def f (r : ZMod p) : (short A B).Point := d.pt r.val

variable [hp : Fact p.Prime]

omit [DecidableEq L] [CharZero L] in
lemma natCast_ne {n : ℕ} (h0 : 0 < n) (hn : n < p) : (n : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h; exact absurd (Nat.le_of_dvd h0 h) (by omega)

lemma f_zero : d.f 0 = 0 := by simp [f, ZMod.val_zero, d.pt_zero]

lemma f_ne {r : ZMod p} (hr : r ≠ 0) : d.f r ≠ 0 :=
  d.pt_ne (Nat.one_le_iff_ne_zero.mpr ((ZMod.val_ne_zero r).mpr hr)) (ZMod.val_lt r)

lemma f_neg (r : ZMod p) : d.f (-r) = -d.f r := by
  by_cases hr : r = 0
  · subst hr; simp [d.f_zero]
  have h1 : 1 ≤ r.val := Nat.one_le_iff_ne_zero.mpr ((ZMod.val_ne_zero r).mpr hr)
  rw [f, f, d.neg_pt h1 (ZMod.val_lt r), ZMod.neg_val, if_neg hr]

lemma f_add_ne {r s : ZMod p} (hr : r ≠ 0) (hs : s ≠ 0) (hrs : r ≠ s) (h0 : r + s ≠ 0) :
    d.f r + d.f s = d.f (r + s) := by
  have h1 : 1 ≤ r.val := Nat.one_le_iff_ne_zero.mpr ((ZMod.val_ne_zero r).mpr hr)
  have h2 : 1 ≤ s.val := Nat.one_le_iff_ne_zero.mpr ((ZMod.val_ne_zero s).mpr hs)
  have hv : r.val ≠ s.val := fun h => hrs (ZMod.val_injective p h)
  have hsum : r.val + s.val ≠ p := by
    intro h; apply h0
    rw [← ZMod.natCast_zmod_val r, ← ZMod.natCast_zmod_val s, ← Nat.cast_add, h, ZMod.natCast_self]
  rw [f, f, f, ZMod.val_add, d.pt_add_ne h1 (ZMod.val_lt r) h2 (ZMod.val_lt s) hv hsum]

/-- **`k ↦ P_k` is a homomorphism** (`p ≥ 5`). -/
theorem f_add (hp5 : 5 ≤ p) (r s : ZMod p) : d.f (r + s) = d.f r + d.f s := by
  have h2 : (2 : ZMod p) ≠ 0 := by exact_mod_cast natCast_ne (p := p) (n := 2) (by omega) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 := by exact_mod_cast natCast_ne (p := p) (n := 3) (by omega) (by omega)
  by_cases hr : r = 0
  · subst hr; simp [d.f_zero]
  by_cases hs : s = 0
  · subst hs; simp [d.f_zero]
  by_cases h0 : r + s = 0
  · rw [h0, d.f_zero, eq_neg_of_add_eq_zero_right h0, d.f_neg]; simp
  by_cases hrs : r = s
  · subst hrs
    -- `P_r = P_{2r} + P_{−r}`
    have h2r : 2 * r ≠ 0 := mul_ne_zero h2 hr
    have key := d.f_add_ne (r := 2 * r) (s := -r) h2r (neg_ne_zero.mpr hr)
      (by intro h; apply mul_ne_zero h3 hr; linear_combination h)
      (by intro h; apply hr; linear_combination h)
    rw [show 2 * r + -r = r by ring, d.f_neg] at key
    rw [show r + r = 2 * r by ring]
    nth_rewrite 1 [← key]
    abel
  · exact (d.f_add_ne hr hs hrs h0).symm

lemma f_injective (hp5 : 5 ≤ p) : Function.Injective d.f := by
  intro r s h
  by_contra hne
  have := d.f_add hp5 (r - s) s
  rw [sub_add_cancel, h] at this
  exact d.f_ne (sub_ne_zero.mpr hne) (by simpa using this.symm)

lemma f_natCast {k : ℕ} (hk : k < p) : d.f (k : ZMod p) = d.pt k := by
  rw [f, ZMod.val_natCast_of_lt hk]

lemma pt_injOn (hp5 : 5 ≤ p) {a b : ℕ} (ha : a < p) (hb : b < p) (h : d.pt a = d.pt b) : a = b := by
  rw [← d.f_natCast ha, ← d.f_natCast hb] at h
  have := d.f_injective hp5 h
  rwa [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

/-! ### The kernel -/

/-- **The Vélu kernel** `{P_k}`. -/
def kernel (hp5 : 5 ≤ p) : Kernel A B where
  G := univ.image d.f
  S := (Icc 1 (p / 2)).image d.pt
  zero_mem := mem_image.mpr ⟨0, mem_univ _, d.f_zero⟩
  add_mem P hP Q hQ := by
    obtain ⟨r, -, rfl⟩ := mem_image.mp hP
    obtain ⟨s, -, rfl⟩ := mem_image.mp hQ
    exact mem_image.mpr ⟨r + s, mem_univ _, d.f_add hp5 r s⟩
  neg_mem P hP := by
    obtain ⟨r, -, rfl⟩ := mem_image.mp hP
    exact mem_image.mpr ⟨-r, mem_univ _, d.f_neg r⟩
  no_two_torsion P hP h := by
    obtain ⟨r, -, rfl⟩ := mem_image.mp hP
    rw [← d.f_add hp5] at h
    by_contra hne
    have hr : r ≠ 0 := fun h' => hne (by rw [h', d.f_zero])
    have h2 : (2 : ZMod p) ≠ 0 := by
      exact_mod_cast natCast_ne (p := p) (n := 2) (by omega) (by omega)
    exact d.f_ne (show r + r ≠ 0 by rw [← two_mul]; exact mul_ne_zero h2 hr) h
  S_sub := by
    intro Q hQ
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hQ
    rw [mem_Icc] at hk
    exact mem_image.mpr ⟨k, mem_univ _, d.f_natCast (by omega)⟩
  zero_not_mem_S := by
    intro h
    obtain ⟨k, hk, hk0⟩ := mem_image.mp h
    rw [mem_Icc] at hk
    exact d.pt_ne hk.1 (by omega) hk0
  neg_not_mem_S := by
    intro Q hQ h
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hQ
    obtain ⟨l, hl, hl'⟩ := mem_image.mp h
    rw [mem_Icc] at hk hl
    rw [d.neg_pt hk.1 (by omega)] at hl'
    have := d.pt_injOn hp5 (by omega) (by omega) hl'
    have hodd : p % 2 = 1 := (hp.out.eq_two_or_odd).resolve_left (by omega)
    omega
  cover := by
    intro P hP hP0
    obtain ⟨r, -, rfl⟩ := mem_image.mp hP
    have hr : r ≠ 0 := fun h' => hP0 (by rw [h', d.f_zero])
    have h1 : 1 ≤ r.val := Nat.one_le_iff_ne_zero.mpr ((ZMod.val_ne_zero r).mpr hr)
    have hlt := ZMod.val_lt r
    have hodd : p % 2 = 1 := (hp.out.eq_two_or_odd).resolve_left (by omega)
    by_cases hk : r.val ≤ p / 2
    · exact Or.inl (mem_image.mpr ⟨r.val, mem_Icc.mpr ⟨h1, hk⟩, rfl⟩)
    · refine Or.inr (mem_image.mpr ⟨p - r.val, mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩)
      rw [f, d.neg_pt h1 hlt]

lemma kernel_G (hp5 : 5 ≤ p) : (d.kernel hp5).G = univ.image d.f := by simp [kernel]

lemma kernel_card (hp5 : 5 ≤ p) : (d.kernel hp5).G.card = p := by
  rw [kernel_G, card_image_of_injective _ (d.f_injective hp5), card_univ, ZMod.card]

lemma mem_kernel (hp5 : 5 ≤ p) {Q : (short A B).Point} :
    Q ∈ (d.kernel hp5).G ↔ Q = 0 ∨ ∃ k, 1 ≤ k ∧ k < p ∧ Q = d.pt k := by
  rw [kernel_G, mem_image]
  constructor
  · rintro ⟨r, -, rfl⟩
    by_cases hr : r = 0
    · left; rw [hr, d.f_zero]
    · right
      exact ⟨r.val, Nat.one_le_iff_ne_zero.mpr ((ZMod.val_ne_zero r).mpr hr), ZMod.val_lt r, rfl⟩
  · rintro (rfl | ⟨k, -, hk, rfl⟩)
    · exact ⟨0, mem_univ _, d.f_zero⟩
    · exact ⟨k, mem_univ _, d.f_natCast hk⟩

lemma sum_S (hp5 : 5 ≤ p) (g : (short A B).Point → L) :
    ∑ Q ∈ (d.kernel hp5).S, g Q = ∑ k ∈ Icc 1 (p / 2), g (d.pt k) := by
  show ∑ Q ∈ (Icc 1 (p / 2)).image d.pt, g Q = _
  rw [sum_image]
  intro a ha b hb h
  rw [coe_Icc, Set.mem_Icc] at ha hb
  exact d.pt_injOn hp5 (by omega) (by omega) h

lemma kernel_A' (hp5 : 5 ≤ p) : (d.kernel hp5).A' = TateQuot.veluA A (Icc 1 (p / 2)) d.X := by
  rw [TateQuot.kernel_A', TateQuot.veluA, TateQuot.veluA, d.sum_S hp5 (fun Q => 6 * xc Q ^ 2 + 2 * A)]
  congr 2
  refine sum_congr rfl fun k hk => ?_
  rw [mem_Icc] at hk
  rw [d.xc_pt hk.1 (by omega)]

lemma kernel_B' (hp5 : 5 ≤ p) :
    (d.kernel hp5).B' = TateQuot.veluB A B (Icc 1 (p / 2)) d.X d.Y := by
  rw [TateQuot.kernel_B', TateQuot.veluB, TateQuot.veluB,
    d.sum_S hp5 (fun Q => 4 * yc Q ^ 2 + xc Q * (6 * xc Q ^ 2 + 2 * A))]
  congr 2
  refine sum_congr rfl fun k hk => ?_
  rw [mem_Icc] at hk
  rw [d.xc_pt hk.1 (by omega), d.yc_pt hk.1 (by omega)]

end TorsData

end TateAdd
