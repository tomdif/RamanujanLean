/-
# A single isometry from short dual phase partners

Equal-norm, equal-phase partners on a spanning family determine a single
orthogonal involution. The partner map and its involutivity are conclusions,
not hypotheses. Existence of partners and the spanning property still have
to be supplied by the analytic and lattice-generation arguments.
-/
import RamanujanTau.MultiQuintupleDualShortGeometry
import RamanujanTau.MultiQuintupleSpanningIsometry

namespace Ramanujan.MultiQuintuple

theorem ternaryRatDot_intIndexToRat (x y : TernaryIntPoint) :
    ternaryRatDot (ternaryIntIndexToRat x) (ternaryIntIndexToRat y) =
      (ternaryIntDot x y : ℚ) := by
  simp [ternaryRatDot, ternaryIntIndexToRat, ternaryIntDot, ternaryDot]

@[simp] theorem ternaryIntIndexToRat_neg (x : TernaryIntPoint) :
    ternaryIntIndexToRat (-x) = -ternaryIntIndexToRat x := by
  simp [ternaryIntIndexToRat]

namespace ProjectiveDualLift

theorem phase_neg_of_point_neg {p : ℕ} [Fact p.Prime] {v : TernaryIntPoint}
    (x y : ProjectiveDualLift p v) (hvi : (v.1.1 : ZMod p) ≠ 0)
    (h : ℤ) (hv : ternaryIntNorm v = (p : ℤ)*h) (c : ZMod p)
    (hpoint : y.point = -x.point) : y.phase c = -x.phase c := by
  have hxs : (x.point.1.1 : ZMod p) = (x.scalar : ZMod p)*v.1.1 := by
    rw [x.point_eq]
    simp
  have hys : (y.point.1.1 : ZMod p) = (y.scalar : ZMod p)*v.1.1 := by
    rw [y.point_eq]
    simp
  have hs : (y.scalar : ZMod p) = -(x.scalar : ZMod p) := by
    apply mul_right_cancel₀ hvi
    rw [← hys, neg_mul, ← hxs, hpoint]
    simp
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hxpair : (p : ℤ)*x.pairing = ternaryIntDot v x.point := by
    rw [x.pairing_eq hp h hv, x.dot_base h hv]
  have hypair : (p : ℤ)*y.pairing = ternaryIntDot v y.point := by
    rw [y.pairing_eq hp h hv, y.dot_base h hv]
  have hd : ternaryIntDot v y.point = -ternaryIntDot v x.point := by
    rw [hpoint]
    simp [ternaryIntDot, ternaryDot]
    ring
  have hpair : y.pairing = -x.pairing := by
    apply mul_left_cancel₀ (show (p : ℤ) ≠ 0 by exact_mod_cast hp)
    rw [mul_neg, hypair, hxpair, hd]
  simp only [phase, hs, hpair, Int.cast_neg]
  ring

/-- A nonzero phase excludes the central antipode as a phase partner. -/
theorem phase_partner_ne_neg {p : ℕ} [Fact p.Prime] {v : TernaryIntPoint}
    (x y : ProjectiveDualLift p v) (hpodd : Odd (p : ℤ))
    (hvi : (v.1.1 : ZMod p) ≠ 0) (h : ℤ)
    (hv : ternaryIntNorm v = (p : ℤ)*h) (c : ZMod p)
    (hphase : y.phase c = x.phase c) (hnonzero : x.phase c ≠ 0) :
    y.point ≠ -x.point := by
  intro heq
  have hneg := x.phase_neg_of_point_neg y hvi h hv c heq
  have h2 : (2 : ZMod p) ≠ 0 := by
    have hp : p.Prime := Fact.out
    have hp2 : p ≠ 2 := by intro heq; subst p; norm_num [Odd] at hpodd
    exact (ZMod.natCast_eq_zero_iff 2 p).not.mpr (by
      intro hd
      rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd with hh | hh
      · exact hp.ne_one hh
      · exact hp2 hh)
  have hz : (2 : ZMod p)*x.phase c = 0 := by
    linear_combination hneg - hphase
  exact hnonzero ((mul_eq_zero.mp hz).resolve_left h2)

end ProjectiveDualLift

/-- Short partners assemble into one noncentral orthogonal involution.
The arithmetic proves both preservation of every Gram entry and uniqueness
of partners, so no coherence or involutivity assumption is needed. -/
theorem short_phase_partners_yield_orthogonal_involution
    {ι : Type*} {p : ℕ} [Fact p.Prime] {v : TernaryIntPoint}
    (x : ι → ProjectiveDualLift p v) (hpodd : Odd (p : ℤ))
    (hvi : (v.1.1 : ZMod p) ≠ 0) (h : ℤ)
    (hv : ternaryIntNorm v = (p : ℤ)*h) (c : ZMod p)
    (hshort : ∀ i, 2*ternaryIntNorm (x i).point < (p : ℤ)^2)
    (hspan : Submodule.span ℚ (Set.range (fun i => ternaryIntIndexToRat (x i).point)) = ⊤)
    (hpartner : ∀ i, ∃ j,
      ternaryIntNorm (x j).point = ternaryIntNorm (x i).point ∧
      (x j).point ≠ (x i).point ∧ (x j).phase c = (x i).phase c)
    (hnonzero : ∃ i, (x i).phase c ≠ 0) :
    ∃ T : RationalTernaryOrthogonalInvolution, ∀ i, ∃ j,
      T.linear (ternaryIntIndexToRat (x i).point) = ternaryIntIndexToRat (x j).point ∧
      ternaryIntNorm (x j).point = ternaryIntNorm (x i).point ∧
      (x j).point ≠ (x i).point ∧ (x j).phase c = (x i).phase c := by
  classical
  choose f hf using hpartner
  let a := fun i => ternaryIntIndexToRat (x i).point
  obtain ⟨T,hT,hdot⟩ := exists_linear_of_spanning_gram_family a (fun i => a (f i)) hspan (by
    intro i j
    simp only [a, ternaryRatDot_intIndexToRat]
    exact_mod_cast (x i).short_phase_partners_preserve_dot (x j) (x (f i)) (x (f j))
      hpodd h hv c (hf i).1 (hf j).1 (hshort i) (hshort j)
      (hf i).2.1 (hf j).2.1 (hf i).2.2 (hf j).2.2)
  have hfi : ∀ i, (x (f (f i))).point = (x i).point := by
    intro i
    exact (x (f i)).short_phase_partner_unique (x (f (f i))) (x i) hpodd h hv c
      (hf (f i)).1 (hf i).1.symm (hshort (f i))
      (hf (f i)).2.1 (hf i).2.1.symm (hf (f i)).2.2 (hf i).2.2.symm
  have hinvol : ∀ z, T (T z) = z := by
    intro z
    have hz : z ∈ Submodule.span ℚ (Set.range a) := by rw [hspan]; trivial
    induction hz using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨i,rfl⟩ := hz
        rw [hT, hT]
        exact congrArg ternaryIntIndexToRat (hfi i)
    | zero => simp
    | add u v hu hv iu iv => simp only [map_add, iu, iv]
    | smul r u hu iu => simp only [map_smul, iu]
  obtain ⟨i,hi⟩ := hnonzero
  have hne : T (a i) ≠ a i := by
    rw [hT]
    exact fun heq => (hf i).2.1 (ternaryIntIndexToRat_injective heq)
  have hneneg : T (a i) ≠ -a i := by
    rw [hT]
    intro heq
    have hnegpoint : (x (f i)).point = -(x i).point := by
      apply ternaryIntIndexToRat_injective
      simpa only [ternaryIntIndexToRat_neg] using heq
    exact (x i).phase_partner_ne_neg (x (f i)) hpodd hvi h hv c (hf i).2.2 hi hnegpoint
  refine ⟨{
    linear := T
    norm_preserving := fun z => by simpa only [ternaryRatDot_self] using hdot z z
    involutive := hinvol
    not_identity := ⟨a i,hne⟩
    not_neg_identity := ⟨a i,hneneg⟩
  }, ?_⟩
  intro j
  exact ⟨f j,hT j,hf j⟩

end Ramanujan.MultiQuintuple
