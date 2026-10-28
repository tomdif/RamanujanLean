/-
# The canonical subgroup as a `FinSub`, and the canonical/non-canonical dichotomy

Break region (`‖p‖^p < ‖a‖^{p+1}`), short `W` with supersingular good reduction.

* `canSub`: `{0} ∪ {canonical points}` (`‖a‖‖z‖^{p−1} = ‖p‖`) is a `Lubin.FinSub` of `T = F[p]`;
* **`card_canSub`**: it has order `p` (Lagrange in `E(K)[p]`: its order divides `p²`, it contains a
  canonical point, and misses a non-canonical one);
* **`eq_canSub`**: an order-`p` subgroup of `T` with one nonzero canonical point is `canSub`.
  So every other order-`p` subgroup has **no** nonzero canonical point.
-/
import RamanujanTau.AllQuotients.Torsion

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AllQuotients
open MvPowerSeries EllipticFormal EllipticI2 CanonicalIsogeny QuotientHasse VeluLubin

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "𝒪" => CanonicalIsogeny.integers K

/-- a canonical point is strictly smaller than a non-canonical one (break region). -/
lemma can_noncan {p : ℕ} {A P X Y : ℝ} (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y) (hA0 : 0 ≤ A)
    (hx : A * X ^ (p - 1) = P) (hy : Y ^ (p * (p - 1)) = A) (hYX : Y ≤ X)
    (hb : P ^ p < A ^ (p + 1)) : False := by
  have : A ^ (p + 1) ≤ P ^ p := by
    calc A ^ (p + 1) = A ^ p * Y ^ (p * (p - 1)) := by rw [hy, pow_succ]
      _ ≤ A ^ p * X ^ (p * (p - 1)) := by gcongr
      _ = P ^ p := by rw [← hx, mul_pow, ← pow_mul, mul_comm (p - 1) p]
  linarith

section Can
variable [IsAlgClosed K] [CharZero K] [DecidableEq K] (a b : ↥(CanonicalIsogeny.integers K))

/-- the canonical points of `T`, with `0`. -/
noncomputable def canH (p : ℕ) (T : Finset 𝒪) : Finset 𝒪 :=
  T.filter (fun z => z = 0 ∨
    ‖((hasse (formalGroup (shortO a b)) p : 𝒪) : K)‖ * ‖(z : K)‖ ^ (p - 1) = ‖(p : K)‖)

/-- **the canonical subgroup** as a `FinSub` (break region). -/
noncomputable def canSub {p : ℕ} [hpf : Fact p.Prime] {T : Finset 𝒪}
    (hT : ∀ z, z ∈ T ↔ ‖(z : K)‖ < 1 ∧ nm a b z p = 0)
    (hu : ‖topc (formalGroup (shortO a b)) p‖ = 1) (ha : ‖hasse (formalGroup (shortO a b)) p‖ < 1)
    (hε : 0 < ‖(p : K)‖) (hp1 : ‖(p : K)‖ < 1)
    (hbreak : ‖(p : K)‖ ^ p < ‖hasse (formalGroup (shortO a b)) p‖ ^ (p + 1)) :
    Lubin.FinSub (formalGroup (shortO a b)) where
  H := canH a b p T
  tn := fun h hh => (torsSub a b p T hT).tn h (Finset.mem_filter.1 hh).1
  zero_mem := Finset.mem_filter.2 ⟨(torsSub a b p T hT).zero_mem, Or.inl rfl⟩
  add_mem := fun u hu' v hv' => by
    obtain ⟨huT, hu2⟩ := Finset.mem_filter.1 hu'
    obtain ⟨hvT, hv2⟩ := Finset.mem_filter.1 hv'
    have hwT := (torsSub a b p T hT).add_mem u huT v hvT
    refine Finset.mem_filter.2 ⟨hwT, ?_⟩
    set w := Lubin.padd (formalGroup (shortO a b)) u v
    by_cases hw0 : w = 0
    · exact Or.inl hw0
    right
    have hu1 := ((hT u).1 huT).1
    have hv1 := ((hT v).1 hvT).1
    obtain ⟨hw1, hwp⟩ := (hT w).1 hwT
    rcases (classify' (formalGroup (shortO a b)) p hu ha hε hp1 hw0 hw1 hwp).1 hbreak with h | h
    · exact h
    exfalso
    have hle := norm_padd_le (formalGroup (shortO a b)) incl continuous_incl norm_incl_le
      (tn_of_norm hu1) (tn_of_norm hv1)
    have hp2 := hpf.out.two_le
    rcases le_max_iff.1 hle with hle | hle
    · rcases hu2 with h0 | hc
      · have h00 : ‖incl u‖ = 0 := by rw [h0]; simp
        exact hw0 (Subtype.ext (norm_le_zero_iff.1 (hle.trans h00.le)))
      · exact can_noncan (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hc h hle hbreak
    · rcases hv2 with h0 | hc
      · have h00 : ‖incl v‖ = 0 := by rw [h0]; simp
        exact hw0 (Subtype.ext (norm_le_zero_iff.1 (hle.trans h00.le)))
      · exact can_noncan (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hc h hle hbreak
  neg_mem := fun u hu' => by
    obtain ⟨huT, hu2⟩ := Finset.mem_filter.1 hu'
    refine ⟨-u, Finset.mem_filter.2 ⟨neg_mem_T a b hT huT, ?_⟩, padd_neg a b ((hT u).1 huT).1⟩
    rcases hu2 with h0 | hc
    · left; rw [h0, neg_zero]
    · right; rw [Subring.coe_neg, norm_neg]; exact hc

lemma canSub_sub {p : ℕ} [Fact p.Prime] {T : Finset 𝒪}
    (hT : ∀ z, z ∈ T ↔ ‖(z : K)‖ < 1 ∧ nm a b z p = 0)
    (hu : ‖topc (formalGroup (shortO a b)) p‖ = 1) (ha : ‖hasse (formalGroup (shortO a b)) p‖ < 1)
    (hε : 0 < ‖(p : K)‖) (hp1 : ‖(p : K)‖ < 1)
    (hbreak : ‖(p : K)‖ ^ p < ‖hasse (formalGroup (shortO a b)) p‖ ^ (p + 1)) :
    (canSub a b hT hu ha hε hp1 hbreak).H ⊆ T := Finset.filter_subset _ _

lemma canSub_can {p : ℕ} [Fact p.Prime] {T : Finset 𝒪}
    (hT : ∀ z, z ∈ T ↔ ‖(z : K)‖ < 1 ∧ nm a b z p = 0)
    (hu : ‖topc (formalGroup (shortO a b)) p‖ = 1) (ha : ‖hasse (formalGroup (shortO a b)) p‖ < 1)
    (hε : 0 < ‖(p : K)‖) (hp1 : ‖(p : K)‖ < 1)
    (hbreak : ‖(p : K)‖ ^ p < ‖hasse (formalGroup (shortO a b)) p‖ ^ (p + 1)) :
    ∀ c ∈ (canSub a b hT hu ha hε hp1 hbreak).H, c ≠ 0 →
      ‖((hasse (formalGroup (shortO a b)) p : 𝒪) : K)‖ * ‖(c : K)‖ ^ (p - 1) = ‖(p : K)‖ :=
  fun c hc hc0 => ((Finset.mem_filter.1 hc).2).resolve_left hc0

lemma nat_card_toAddSubgroup {G : Finset (Velu.short (a : K) (b : K)).Point}
    (hG : SubgroupSum.IsSub G) : Nat.card hG.toAddSubgroup = G.card := by
  change Nat.card (G : Set (Velu.short (a : K) (b : K)).Point) = G.card
  rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]

/-- **the canonical subgroup has order `p`.** -/
theorem card_canSub {p : ℕ} [hpf : Fact p.Prime] (hp5 : 5 ≤ p) {T : Finset 𝒪}
    (hT : ∀ z, z ∈ T ↔ ‖(z : K)‖ < 1 ∧ nm a b z p = 0) (hTc : T.card = p ^ 2)
    (hu : ‖topc (formalGroup (shortO a b)) p‖ = 1) (ha : ‖hasse (formalGroup (shortO a b)) p‖ < 1)
    (hε : 0 < ‖(p : K)‖) (hp1 : ‖(p : K)‖ < 1)
    (hbreak : ‖(p : K)‖ ^ p < ‖hasse (formalGroup (shortO a b)) p‖ ^ (p + 1)) :
    (canSub a b hT hu ha hε hp1 hbreak).H.card = p := by
  classical
  have hp := hpf.out
  set C := canSub a b hT hu ha hε hp1 hbreak
  have hCT : C.H ⊆ T := canSub_sub a b hT hu ha hε hp1 hbreak
  have hG₀ := isSub_image a b hp hp5 hT C hCT
  have hT' := isSub_image a b hp hp5 hT (torsSub a b p T hT) subset_rfl
  have hle : hG₀.toAddSubgroup ≤ hT'.toAddSubgroup := fun P hP =>
    Finset.image_subset_image hCT hP
  have hdvd := AddSubgroup.card_dvd_of_le hle
  rw [nat_card_toAddSubgroup, nat_card_toAddSubgroup] at hdvd
  change (C.H.image (Pt a b)).card ∣ (T.image (Pt a b)).card at hdvd
  rw [Finset.card_image_of_injOn ((Pt_injOn a b hp hp5 hT).mono (by exact_mod_cast hCT)),
    Finset.card_image_of_injOn (Pt_injOn a b hp hp5 hT)] at hdvd
  rw [hTc] at hdvd
  obtain ⟨k, hk, hkc⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  obtain ⟨⟨y, hy0, hy1, hyp, hyc⟩, ⟨z, hz0, hz1, hzp, hzc⟩⟩ :=
    torsion_exists (formalGroup (shortO a b)) p hu ha hε hp1 hbreak
  interval_cases k
  · exfalso
    have hyC : y ∈ C.H := Finset.mem_filter.2 ⟨(hT y).2 ⟨hy1, hyp⟩, Or.inr hyc⟩
    have h1 : C.H.card ≤ 1 := by rw [hkc]; simp
    exact hy0 (Finset.card_le_one.1 h1 y hyC 0 C.zero_mem)
  · simpa using hkc
  · exfalso
    have heq : C.H = T := Finset.eq_of_subset_of_card_le hCT (by rw [hkc, hTc])
    have hzC : z ∈ C.H := heq ▸ (hT z).2 ⟨hz1, hzp⟩
    rcases (Finset.mem_filter.1 hzC).2 with h0 | hc
    · exact hz0 h0
    · have hp2 := hp.two_le
      have e : p ^ 2 - p = p * (p - 1) := by
        rw [Nat.mul_sub, mul_one, sq]
      rw [e] at hzc
      exact can_noncan (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hc hzc le_rfl hbreak

/-- **uniqueness**: an order-`p` subgroup of `T` with a nonzero canonical point is `canSub`. -/
theorem eq_canSub {p : ℕ} [hpf : Fact p.Prime] (hp5 : 5 ≤ p) {T : Finset 𝒪}
    (hT : ∀ z, z ∈ T ↔ ‖(z : K)‖ < 1 ∧ nm a b z p = 0) (hTc : T.card = p ^ 2)
    (hu : ‖topc (formalGroup (shortO a b)) p‖ = 1) (ha : ‖hasse (formalGroup (shortO a b)) p‖ < 1)
    (hε : 0 < ‖(p : K)‖) (hp1 : ‖(p : K)‖ < 1)
    (hbreak : ‖(p : K)‖ ^ p < ‖hasse (formalGroup (shortO a b)) p‖ ^ (p + 1))
    (C : Lubin.FinSub (formalGroup (shortO a b))) (hCT : C.H ⊆ T) (hcard : C.H.card = p)
    {x : 𝒪} (hxC : x ∈ C.H) (hx0 : x ≠ 0)
    (hxc : ‖((hasse (formalGroup (shortO a b)) p : 𝒪) : K)‖ * ‖(x : K)‖ ^ (p - 1) = ‖(p : K)‖) :
    C.H = (canSub a b hT hu ha hε hp1 hbreak).H := by
  have hp := hpf.out
  have hxT := hCT hxC
  have hpx := ((hT x).1 hxT).2
  have hxH : x ∈ (canSub a b hT hu ha hε hp1 hbreak).H := Finset.mem_filter.2 ⟨hxT, Or.inr hxc⟩
  exact (eq_cyc a b hp C hcard hxC hx0 hpx).trans
    (eq_cyc a b hp _ (card_canSub a b hp5 hT hTc hu ha hε hp1 hbreak) hxH hx0 hpx).symm

end Can

end AllQuotients
