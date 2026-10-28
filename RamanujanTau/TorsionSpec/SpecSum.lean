import RamanujanTau.TorsionSpec.Spec
import RamanujanTau.TorsionSpec.R1

/-!
# Specialization of the subgroup sum

Given specialization data `D` (`Spec.lean`) with `ℚ ⊆ O`, and finite sets `T_L = E[n](L)`,
`T_K = Ē[n](K)` with `|T_K| ≤ |T_L|`, the specialization map is a bijection `E[n](L) → Ē[n](K)`
compatible with the group law, hence `G ↦ sp(G)` is a bijection between subgroups of order `n`, and
(**`ev_subSum`**) the subgroup sum over `L` lies in `O` and specializes to the subgroup sum over `K`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TorsionSpec

open Velu SubgroupSum WeierstrassCurve WeierstrassCurve.Affine

namespace SpecData

variable {L K : Type*} [Field L] [Field K] [DecidableEq L] [DecidableEq K] [CharZero K]
  {A B : L} {a b : K} (D : SpecData L K A B a b)

open scoped Classical in
/-- Evaluation of `ψ` on elements of `L` (junk `0` off `O`). -/
noncomputable def ev (z : L) : K := if h : z ∈ D.O then D.ψ ⟨z, h⟩ else 0

lemma ev_of {z : L} (hz : z ∈ D.O) : D.ev z = D.ψ ⟨z, hz⟩ := dif_pos hz

lemma ev_add {z w : L} (hz : z ∈ D.O) (hw : w ∈ D.O) : D.ev (z + w) = D.ev z + D.ev w := by
  rw [D.ev_of hz, D.ev_of hw, D.ev_of (add_mem hz hw), ← map_add]; rfl

lemma ev_mul {z w : L} (hz : z ∈ D.O) (hw : w ∈ D.O) : D.ev (z * w) = D.ev z * D.ev w := by
  rw [D.ev_of hz, D.ev_of hw, D.ev_of (mul_mem hz hw), ← map_mul]; rfl

lemma ev_neg {z : L} (hz : z ∈ D.O) : D.ev (-z) = -D.ev z := by
  rw [D.ev_of hz, D.ev_of (neg_mem hz), ← map_neg]; rfl

lemma ev_sub {z w : L} (hz : z ∈ D.O) (hw : w ∈ D.O) : D.ev (z - w) = D.ev z - D.ev w := by
  rw [sub_eq_add_neg, D.ev_add hz (neg_mem hw), D.ev_neg hw, ← sub_eq_add_neg]

lemma ev_pow {z : L} (hz : z ∈ D.O) (m : ℕ) : D.ev (z ^ m) = D.ev z ^ m := by
  rw [D.ev_of hz, D.ev_of (pow_mem hz m), ← map_pow]; rfl

lemma ev_intCast (m : ℤ) : D.ev (m : L) = m := by
  rw [D.ev_of (intCast_mem D.O m)]
  rw [show (⟨(m : L), intCast_mem D.O m⟩ : D.O) = (m : D.O) from Subtype.ext (by simp), map_intCast]

lemma ev_natCast (m : ℕ) : D.ev (m : L) = m := by
  have := D.ev_intCast m; simpa using this

lemma ev_ofNat (m : ℕ) [m.AtLeastTwo] : D.ev (OfNat.ofNat m : L) = OfNat.ofNat m := by
  have := D.ev_natCast m; simpa using this

lemma ofNat_mem (m : ℕ) [m.AtLeastTwo] : (OfNat.ofNat m : L) ∈ D.O := by
  have := natCast_mem D.O m; simpa using this

lemma ev_A : D.ev A = a := by rw [D.ev_of D.hA, D.ψA]
lemma ev_B : D.ev B = b := by rw [D.ev_of D.hB, D.ψB]

lemma ev_zero : D.ev 0 = 0 := by simpa using D.ev_natCast 0

lemma ev_sum {ι : Type*} (s : Finset ι) (f : ι → L) (hf : ∀ i ∈ s, f i ∈ D.O) :
    (∑ i ∈ s, f i) ∈ D.O ∧ D.ev (∑ i ∈ s, f i) = ∑ i ∈ s, D.ev (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using D.ev_zero
  | insert j s hj ih =>
    have hs := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hfj := hf j (Finset.mem_insert_self j s)
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact ⟨add_mem hfj hs.1, by rw [D.ev_add hfj hs.1, hs.2]⟩

section Rat
variable [Algebra ℚ L] (hrat : ∀ q : ℚ, algebraMap ℚ L q ∈ D.O)
include hrat

lemma ev_rat (q : ℚ) : D.ev (algebraMap ℚ L q) = algebraMap ℚ K q := by
  have hden : (q.den : K) ≠ 0 := by exact_mod_cast q.den_nz
  have e : algebraMap ℚ L q * (q.den : L) = (q.num : L) := by
    rw [show (q.den : L) = algebraMap ℚ L q.den by simp,
      show (q.num : L) = algebraMap ℚ L q.num by simp, ← map_mul, Rat.mul_den_eq_num]
  have := congrArg D.ev e
  rw [D.ev_mul (hrat q) (natCast_mem D.O _), D.ev_natCast, D.ev_intCast] at this
  rw [eq_ratCast (algebraMap ℚ K) q, Rat.cast_def, eq_div_iff hden]; exact this

lemma ev_aeval (Φ : MvPolynomial (Fin 2) ℚ) (v : Fin 2 → L) (hv : ∀ i, v i ∈ D.O) :
    MvPolynomial.aeval v Φ ∈ D.O ∧
      D.ev (MvPolynomial.aeval v Φ) = MvPolynomial.aeval (fun i => D.ev (v i)) Φ := by
  induction Φ using MvPolynomial.induction_on with
  | C q => simp only [MvPolynomial.aeval_C]; exact ⟨hrat q, D.ev_rat hrat q⟩
  | add p q hp hq =>
    simp only [map_add]; exact ⟨add_mem hp.1 hq.1, by rw [D.ev_add hp.1 hq.1, hp.2, hq.2]⟩
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X]
    exact ⟨mul_mem hp.1 (hv i), by rw [D.ev_mul hp.1 (hv i), hp.2]⟩

lemma half_mem : (2 : L)⁻¹ ∈ D.O := by
  have := hrat 2⁻¹; simpa using this

lemma ev_half : D.ev (2 : L)⁻¹ = 2⁻¹ := by
  have := D.ev_rat hrat 2⁻¹; simpa using this

end Rat

/-! ### Points -/

lemma yc_mem {P : (short A B).Point} (hP : IsTors P) : yc P ∈ D.O := by
  rcases P with _ | ⟨x, y, h⟩
  · exact zero_mem _
  · exact (D.mem_of_tors hP).2

lemma xc_sp {P : (short A B).Point} (hP : IsTors P) : xc (D.sp P) = D.ev (xc P) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact D.ev_zero.symm
  · obtain ⟨hx, hy⟩ := D.mem_of_tors hP
    rw [D.sp_some h hx hy, xc_some, xc_some, D.ev_of hx]

lemma yc_sp {P : (short A B).Point} (hP : IsTors P) : yc (D.sp P) = D.ev (yc P) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact D.ev_zero.symm
  · obtain ⟨hx, hy⟩ := D.mem_of_tors hP
    rw [D.sp_some h hx hy, yc_some, yc_some, D.ev_of hy]

lemma sp_eq_zero_iff {P : (short A B).Point} (hP : IsTors P) : D.sp P = 0 ↔ P = 0 :=
  ⟨fun h => by_contra fun h0 => D.sp_ne_zero hP h0 h, fun h => h ▸ D.sp_zero⟩

lemma sp_nsmul {P : (short A B).Point} (hP : IsTors P) (k : ℕ) : D.sp (k • P) = k • D.sp P := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨m, hm, hmP⟩ := hP
    have hk : IsTors (k • P) := ⟨m, hm, by rw [← mul_nsmul, mul_nsmul', hmP, nsmul_zero]⟩
    rw [succ_nsmul, D.sp_add hk ⟨m, hm, hmP⟩, ih, succ_nsmul]

/-- Sums over `sp(G) ∖ 0` pull back to `G ∖ 0`. -/
lemma sum_image_sp (G : Finset (short A B).Point) (hG : ∀ P ∈ G, IsTors P)
    (F : (short a b).Point → K) :
    ∑ Q ∈ (G.image D.sp).erase 0, F Q = ∑ P ∈ G.erase 0, F (D.sp P) := by
  have e : (G.image D.sp).erase 0 = (G.erase 0).image D.sp := by
    ext Q
    simp only [Finset.mem_erase, Finset.mem_image]
    constructor
    · rintro ⟨h0, P, hP, rfl⟩
      exact ⟨P, ⟨fun h => h0 (by rw [h, sp_zero]), hP⟩, rfl⟩
    · rintro ⟨P, ⟨h0, hP⟩, rfl⟩
      exact ⟨D.sp_ne_zero (hG P hP) h0, P, hP, rfl⟩
  rw [e, Finset.sum_image]
  intro P hP Q hQ h
  exact D.sp_inj (hG P (Finset.mem_of_mem_erase hP)) (hG Q (Finset.mem_of_mem_erase hQ)) h

section Coeffs
variable [Algebra ℚ L] (hrat : ∀ q : ℚ, algebraMap ℚ L q ∈ D.O)
include hrat

lemma aC_sp (G : Finset (short A B).Point) (hG : ∀ P ∈ G, IsTors P) :
    aC G ∈ D.O ∧ D.ev (aC G) = aC (G.image D.sp) := by
  have ht : ∀ P ∈ G.erase 0, Kernel.tQ (A := A) (B := B) P ∈ D.O := fun P hP => by
    have hx := D.tors P (hG P (Finset.mem_of_mem_erase hP))
    rw [Kernel.tQ]; exact add_mem (mul_mem (D.ofNat_mem 6) (pow_mem hx 2)) (mul_mem (D.ofNat_mem 2) D.hA)
  obtain ⟨hs, hes⟩ := D.ev_sum (G.erase 0) _ ht
  have h2 := D.half_mem hrat
  have hmem : aC G ∈ D.O := by
    rw [aC, div_eq_mul_inv]; exact sub_mem D.hA (mul_mem (mul_mem (D.ofNat_mem 5) hs) h2)
  refine ⟨hmem, ?_⟩
  rw [aC, aC, tSum, tSum, D.sum_image_sp G hG, div_eq_mul_inv, div_eq_mul_inv,
    D.ev_sub D.hA (mul_mem (mul_mem (D.ofNat_mem 5) hs) h2), D.ev_mul (mul_mem (D.ofNat_mem 5) hs) h2,
    D.ev_mul (D.ofNat_mem 5) hs, hes, D.ev_half hrat, D.ev_A, D.ev_ofNat]
  congr 3
  refine Finset.sum_congr rfl fun P hP => ?_
  have hx := D.tors P (hG P (Finset.mem_of_mem_erase hP))
  rw [Kernel.tQ, Kernel.tQ, D.xc_sp (hG P (Finset.mem_of_mem_erase hP)),
    D.ev_add (mul_mem (D.ofNat_mem 6) (pow_mem hx 2)) (mul_mem (D.ofNat_mem 2) D.hA),
    D.ev_mul (D.ofNat_mem 6) (pow_mem hx 2), D.ev_mul (D.ofNat_mem 2) D.hA, D.ev_pow hx, D.ev_A,
    D.ev_ofNat, D.ev_ofNat]

lemma bC_sp (G : Finset (short A B).Point) (hG : ∀ P ∈ G, IsTors P) :
    bC G ∈ D.O ∧ D.ev (bC G) = bC (G.image D.sp) := by
  have hw : ∀ P ∈ G.erase 0, Kernel.uQ (A := A) (B := B) P + xc P * Kernel.tQ (A := A) (B := B) P
      ∈ D.O := fun P hP => by
    have hP' := hG P (Finset.mem_of_mem_erase hP)
    have hx := D.tors P hP'
    have hy := D.yc_mem hP'
    rw [Kernel.tQ, Kernel.uQ]
    exact add_mem (mul_mem (D.ofNat_mem 4) (pow_mem hy 2))
      (mul_mem hx (add_mem (mul_mem (D.ofNat_mem 6) (pow_mem hx 2)) (mul_mem (D.ofNat_mem 2) D.hA)))
  obtain ⟨hs, hes⟩ := D.ev_sum (G.erase 0) _ hw
  have h2 := D.half_mem hrat
  have hmem : bC G ∈ D.O := by
    rw [bC, div_eq_mul_inv]; exact sub_mem D.hB (mul_mem (mul_mem (D.ofNat_mem 7) hs) h2)
  refine ⟨hmem, ?_⟩
  rw [bC, bC, wSum, wSum, D.sum_image_sp G hG, div_eq_mul_inv, div_eq_mul_inv,
    D.ev_sub D.hB (mul_mem (mul_mem (D.ofNat_mem 7) hs) h2), D.ev_mul (mul_mem (D.ofNat_mem 7) hs) h2,
    D.ev_mul (D.ofNat_mem 7) hs, hes, D.ev_half hrat, D.ev_B, D.ev_ofNat]
  congr 3
  refine Finset.sum_congr rfl fun P hP => ?_
  have hP' := hG P (Finset.mem_of_mem_erase hP)
  have hx := D.tors P hP'
  have hy := D.yc_mem hP'
  rw [Kernel.tQ, Kernel.tQ, Kernel.uQ, Kernel.uQ, D.xc_sp hP', D.yc_sp hP',
    D.ev_add (mul_mem (D.ofNat_mem 4) (pow_mem hy 2))
      (mul_mem hx (add_mem (mul_mem (D.ofNat_mem 6) (pow_mem hx 2)) (mul_mem (D.ofNat_mem 2) D.hA))),
    D.ev_mul (D.ofNat_mem 4) (pow_mem hy 2), D.ev_mul hx (add_mem (mul_mem (D.ofNat_mem 6) (pow_mem hx 2))
      (mul_mem (D.ofNat_mem 2) D.hA)),
    D.ev_add (mul_mem (D.ofNat_mem 6) (pow_mem hx 2)) (mul_mem (D.ofNat_mem 2) D.hA),
    D.ev_mul (D.ofNat_mem 6) (pow_mem hx 2), D.ev_mul (D.ofNat_mem 2) D.hA, D.ev_pow hx, D.ev_pow hy, D.ev_A,
    D.ev_ofNat, D.ev_ofNat, D.ev_ofNat]

end Coeffs

/-! ### The bijection on subgroups -/

omit [CharZero K] in
lemma subs_finite' {n : ℕ} {TK : Finset (short a b).Point} (hTK : ∀ P, P ∈ TK ↔ n • P = 0) :
    (subs a b n).Finite :=
  (TK.powerset.finite_toSet).subset fun H hH =>
    Finset.mem_coe.2 (Finset.mem_powerset.2 fun Q hQ => (hTK Q).2 (nsmul_eq_zero_of_mem_subs hH hQ))

section Bij

variable {n : ℕ} (hn : 0 < n) {TL : Finset (short A B).Point} (hTL : ∀ P, P ∈ TL ↔ n • P = 0)
  {TK : Finset (short a b).Point} (hTK : ∀ P, P ∈ TK ↔ n • P = 0) (hcard : TK.card ≤ TL.card)
include hn hTL

lemma tors_of_mem {P : (short A B).Point} (hP : P ∈ TL) : IsTors P := ⟨n, hn, (hTL P).1 hP⟩

lemma injOn_TL : Set.InjOn D.sp (TL : Set (short A B).Point) := fun P hP Q hQ h =>
  D.sp_inj (tors_of_mem hn hTL hP) (tors_of_mem hn hTL hQ) h

lemma sub_TL {G : Finset (short A B).Point} (hG : G ∈ subs A B n) : G ⊆ TL := fun P hP =>
  (hTL P).2 (nsmul_eq_zero_of_mem_subs hG hP)

include hTK hcard in
lemma image_TL : TL.image D.sp = TK := by
  apply Finset.eq_of_subset_of_card_le
  · intro Q hQ
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hQ
    rw [hTK, ← D.sp_nsmul (tors_of_mem hn hTL hP) n, (hTL P).1 hP, sp_zero]
  · rw [Finset.card_image_of_injOn (D.injOn_TL hn hTL)]; exact hcard

lemma image_mem_subs {G : Finset (short A B).Point} (hG : G ∈ subs A B n) :
    G.image D.sp ∈ subs a b n := by
  have hsub := sub_TL hn hTL hG
  have ht : ∀ P ∈ G, IsTors P := fun P hP => tors_of_mem hn hTL (hsub hP)
  refine ⟨⟨Finset.mem_image.2 ⟨0, hG.1.1, rfl⟩, ?_, ?_⟩, ?_⟩
  · intro P hP Q hQ
    obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 hP
    obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.1 hQ
    exact Finset.mem_image.2 ⟨P' + Q', hG.1.2.1 _ hP' _ hQ', D.sp_add (ht P' hP') (ht Q' hQ')⟩
  · intro P hP
    obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 hP
    exact Finset.mem_image.2 ⟨-P', hG.1.2.2 _ hP', D.sp_neg (ht P' hP')⟩
  · rw [Finset.card_image_of_injOn ((D.injOn_TL hn hTL).mono (by exact_mod_cast hsub)), hG.2]

lemma image_inj {G G' : Finset (short A B).Point} (hG : G ∈ subs A B n) (hG' : G' ∈ subs A B n)
    (h : G.image D.sp = G'.image D.sp) : G = G' := by
  have key : ∀ {G G' : Finset (short A B).Point}, G ∈ subs A B n → G' ∈ subs A B n →
      G.image D.sp = G'.image D.sp → G ⊆ G' := by
    intro G G' hG hG' h P hP
    have : D.sp P ∈ G'.image D.sp := h ▸ Finset.mem_image_of_mem _ hP
    obtain ⟨P', hP', e⟩ := Finset.mem_image.1 this
    rwa [D.injOn_TL hn hTL (sub_TL hn hTL hG' hP') (sub_TL hn hTL hG hP) e] at hP'
  exact Finset.Subset.antisymm (key hG hG' h) (key hG' hG h.symm)

include hTK hcard in
lemma exists_preimage {H : Finset (short a b).Point} (hH : H ∈ subs a b n) :
    ∃ G ∈ subs A B n, G.image D.sp = H := by
  have himg := D.image_TL hn hTL hTK hcard
  set G := TL.filter (fun P => D.sp P ∈ H) with hGdef
  have hGH : G.image D.sp = H := by
    ext Q
    simp only [Finset.mem_image, hGdef, Finset.mem_filter]
    constructor
    · rintro ⟨P, ⟨-, hP⟩, rfl⟩; exact hP
    · intro hQ
      have : Q ∈ TL.image D.sp := by rw [himg, hTK]; exact nsmul_eq_zero_of_mem_subs hH hQ
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 this
      exact ⟨P, ⟨hP, hQ⟩, rfl⟩
  have hGTL : G ⊆ TL := Finset.filter_subset _ _
  have ht : ∀ P ∈ G, IsTors P := fun P hP => tors_of_mem hn hTL (hGTL hP)
  refine ⟨G, ⟨⟨?_, ?_, ?_⟩, ?_⟩, hGH⟩
  · simp only [hGdef, Finset.mem_filter, sp_zero]
    exact ⟨(hTL 0).2 (nsmul_zero n), hH.1.1⟩
  · intro P hP Q hQ
    simp only [hGdef, Finset.mem_filter] at hP hQ ⊢
    refine ⟨(hTL _).2 (by rw [nsmul_add, (hTL P).1 hP.1, (hTL Q).1 hQ.1, add_zero]), ?_⟩
    rw [D.sp_add (tors_of_mem hn hTL hP.1) (tors_of_mem hn hTL hQ.1)]
    exact hH.1.2.1 _ hP.2 _ hQ.2
  · intro P hP
    simp only [hGdef, Finset.mem_filter] at hP ⊢
    refine ⟨(hTL _).2 (by rw [neg_nsmul, (hTL P).1 hP.1, neg_zero]), ?_⟩
    rw [D.sp_neg (tors_of_mem hn hTL hP.1)]
    exact hH.1.2.2 _ hP.2
  · rw [← hH.2, ← hGH, Finset.card_image_of_injOn ((D.injOn_TL hn hTL).mono
      (by exact_mod_cast hGTL))]

lemma subs_finite : (subs A B n).Finite :=
  (TL.powerset.finite_toSet).subset fun G hG =>
    Finset.mem_coe.2 (Finset.mem_powerset.2 (sub_TL hn hTL hG))

include hTK hcard in
/-- **Specialization of the subgroup sum.** -/
theorem ev_subSum [Algebra ℚ L] (hrat : ∀ q : ℚ, algebraMap ℚ L q ∈ D.O)
    (Φ : MvPolynomial (Fin 2) ℚ) :
    subSum n (fun x y => MvPolynomial.aeval (HeckeQExp.ptR (short x y : WeierstrassCurve L)) Φ)
      A B ∈ D.O ∧
    D.ev (subSum n (fun x y => MvPolynomial.aeval (HeckeQExp.ptR (short x y : WeierstrassCurve L)) Φ)
      A B) =
      subSum n (fun x y => MvPolynomial.aeval (HeckeQExp.ptR (short x y : WeierstrassCurve K)) Φ)
        a b := by
  have hfL := subs_finite hn hTL
  have hfK := subs_finite' hTK
  unfold subSum
  rw [dif_pos hfL, dif_pos hfK]
  simp only [ptR_short]
  have hv : ∀ G ∈ hfL.toFinset, ∀ i, (![-48 * aC G, 864 * bC G] : Fin 2 → L) i ∈ D.O := by
    intro G hG i
    rw [Set.Finite.mem_toFinset] at hG
    have ht : ∀ P ∈ G, IsTors P := fun P hP => tors_of_mem hn hTL (sub_TL hn hTL hG hP)
    fin_cases i
    · exact mul_mem (neg_mem (D.ofNat_mem 48)) (D.aC_sp hrat G ht).1
    · exact mul_mem (D.ofNat_mem 864) (D.bC_sp hrat G ht).1
  obtain ⟨hmem, hev⟩ := D.ev_sum hfL.toFinset _ fun G hG => (D.ev_aeval hrat Φ _ (hv G hG)).1
  refine ⟨hmem, ?_⟩
  rw [hev]
  refine Finset.sum_bij (fun G _ => G.image D.sp) ?_ ?_ ?_ ?_
  · intro G hG
    rw [Set.Finite.mem_toFinset] at hG ⊢
    exact D.image_mem_subs hn hTL hG
  · intro G hG G' hG' h
    rw [Set.Finite.mem_toFinset] at hG hG'
    exact D.image_inj hn hTL hG hG' h
  · intro H hH
    rw [Set.Finite.mem_toFinset] at hH
    obtain ⟨G, hG, rfl⟩ := D.exists_preimage hn hTL hTK hcard hH
    exact ⟨G, by rwa [Set.Finite.mem_toFinset], rfl⟩
  · intro G hG
    rw [(D.ev_aeval hrat Φ _ (hv G hG)).2]
    rw [Set.Finite.mem_toFinset] at hG
    have ht : ∀ P ∈ G, IsTors P := fun P hP => tors_of_mem hn hTL (sub_TL hn hTL hG hP)
    congr 2
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [D.ev_mul (neg_mem (D.ofNat_mem 48)) (D.aC_sp hrat G ht).1, D.ev_neg (D.ofNat_mem 48),
        D.ev_ofNat, (D.aC_sp hrat G ht).2]
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [D.ev_mul (D.ofNat_mem 864) (D.bC_sp hrat G ht).1, D.ev_ofNat, (D.bC_sp hrat G ht).2]

end Bij

end SpecData

end TorsionSpec
