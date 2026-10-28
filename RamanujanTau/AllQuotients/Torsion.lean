/-
# The `p`-torsion of `F_W` in the disc, its order-`p` subgroups, and the canonical subgroup

`W : y² = x³ + ax + b` over `𝒪`, `p ≥ 5`, supersingular (`‖a_W‖ < 1`), height `2`.

* `exists_torsion`: the `p`-torsion of the disc is a finite set `T` of cardinality `p²`.
* `cyc`: for `x ≠ 0` in `F[p]`, `⟨x⟩ = {[k]x : k < p}` is a `Lubin.FinSub` of order `p`
  (`card_cyc`); every order-`p` subgroup containing `x` is `⟨x⟩` (`eq_cyc`).
* `torsSub`: `T` as a `Lubin.FinSub`; `Pt` is injective on it with image exactly `E(K)[p]`
  (`Pt_injOn`, `Pt_surj`).
* `ofSub G`: every order-`p` subgroup `G ⊂ E(K)` comes from a unique order-`p` `FinSub` `C ⊂ T`
  with `Pt(C) = G` (`image_ofSub`, `card_ofSub`).
* `canSub`: in the break region the canonical points with `0` form an order-`p` subgroup
  (`card_canSub`), and an order-`p` subgroup with one nonzero canonical point is `canSub`
  (`eq_canSub`).
-/
import RamanujanTau.AllQuotients.Quot
import RamanujanTau.HeckeBridge.Count

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AllQuotients
open MvPowerSeries EllipticFormal EllipticI2 CanonicalIsogeny QuotientHasse VeluLubin

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "𝒪" => CanonicalIsogeny.integers K

/-! ### The torsion set (any height-two formal group) -/

section Tors
variable [IsAlgClosed K]

/-- **the `p`-torsion of the disc has `p²` elements.** -/
theorem exists_torsion (F : FormalGroup 𝒪) [F.IsComm] (p : ℕ) [hp : Fact p.Prime]
    (hu : ‖topc F p‖ = 1) (ha : ‖hasse F p‖ < 1) (hε : 0 < ‖(p : K)‖) (hp1 : ‖(p : K)‖ < 1) :
    ∃ T : Finset 𝒪, (∀ z, z ∈ T ↔
        ‖(z : K)‖ < 1 ∧ Lubin.pt (fun _ : Unit => z) (FGL.nmul F p) = 0) ∧ T.card = p ^ 2 := by
  classical
  have hp2 := hp.out.two_le
  obtain ⟨n, hn, r, U, hU0, hU, hW⟩ := exists_factor F p hu ha hε hp1
  have hS := shape_nmul F p hu
  have hcard : p ^ 2 - 1 = Fintype.card (Fin n) := by rw [Fintype.card_fin, hn]
  have hmN : p - 1 < p ^ 2 - 1 := by
    have : p < p ^ 2 := by nlinarith
    omega
  have hlt : ∀ i, ‖((r i : 𝒪) : K)‖ < 1 :=
    roots_lt_one hS hmN hp1 ha hcard (fun i => ((r i : 𝒪) : K)) U hU0 hU hW
  have hne : ∀ i, r i ≠ 0 := fun i h =>
    roots_ne_zero hS hε (fun i => ((r i : 𝒪) : K)) U hW i (by simp [h])
  have hinj : Function.Injective r := fun i j h =>
    injOn_roots (F := F) incl continuous_incl incl_injective norm_incl_le
      (fun x hx => isTopologicallyNilpotent_of_norm_lt_one hx) p (norm_pos_iff.1 hε) r U hU0 hU hW
      (hlt i) (hlt j) h
  have root := fun {z : 𝒪} (hz : ‖(z : K)‖ < 1) =>
    root_iff (F := F) incl continuous_incl incl_injective norm_incl_le p r U hU0 hU hW
      (isTopologicallyNilpotent_of_norm_lt_one hz) hz
  refine ⟨insert 0 (Finset.univ.image r), fun z => ?_, ?_⟩
  · constructor
    · intro hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact ⟨by simp, (root (by simp)).2 (Or.inl rfl)⟩
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
        exact ⟨hlt i, (root (hlt i)).2 (Or.inr ⟨i, rfl⟩)⟩
    · rintro ⟨h1, h2⟩
      rcases (root h1).1 h2 with rfl | ⟨i, rfl⟩
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  · rw [Finset.card_insert_of_notMem, Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_fin, hn]
    · have : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
    · intro h
      obtain ⟨i, -, hi⟩ := Finset.mem_image.1 h
      exact hne i hi

end Tors

/-! ### Multiples of a point (short curves) -/

section Mult
variable [CharZero K] [DecidableEq K] (a b : ↥(CanonicalIsogeny.integers K))

lemma nm_of_zero (n : ℕ) : nm a b 0 n = 0 := by
  induction n with
  | zero => exact nm_zero a b 0 (by simp)
  | succ n ih => rw [nm_succ a b 0 (by simp), ih, Lubin.padd_zero Lubin.tn0]

lemma nm_padd {x y : 𝒪} (hx : ‖(x : K)‖ < 1) (hy : ‖(y : K)‖ < 1) (n : ℕ) :
    nm a b (Lubin.padd (formalGroup (shortO a b)) x y) n = Lubin.padd (formalGroup (shortO a b)) (nm a b x n) (nm a b y n) :=
  CanonicalIsogeny.pt_nmul_padd n (tn_of_norm hx) (tn_of_norm hy)

lemma nm_nm {x : 𝒪} (hx : ‖(x : K)‖ < 1) (k n : ℕ) : nm a b (nm a b x k) n = nm a b x (k * n) := by
  induction n with
  | zero => rw [mul_zero, nm_zero a b _ (norm_nm a b x hx k), nm_zero a b x hx]
  | succ n ih =>
    rw [nm_succ a b _ (norm_nm a b x hx k), ih, ← nm_add a b x hx]
    congr 1; ring

lemma nm_mod {p : ℕ} {x : 𝒪} (hx : ‖(x : K)‖ < 1) (hpx : nm a b x p = 0) (n : ℕ) :
    nm a b x n = nm a b x (n % p) := by
  conv_lhs => rw [← Nat.div_add_mod n p]
  rw [nm_add a b x hx, nm_mul a b x hx hpx, Lubin.zero_padd (tn_of_norm (norm_nm a b x hx _))]

lemma norm_nm_le {x : 𝒪} (hx : ‖(x : K)‖ < 1) (n : ℕ) : ‖((nm a b x n : 𝒪) : K)‖ ≤ ‖(x : K)‖ := by
  induction n with
  | zero => rw [nm_zero a b x hx]; simp
  | succ n ih =>
    rw [nm_succ a b x hx]
    exact (norm_padd_le (formalGroup (shortO a b)) incl continuous_incl norm_incl_le (tn_of_norm hx)
      (tn_of_norm (norm_nm a b x hx n))).trans (max_le le_rfl ih)

lemma padd_eq_self {z w : 𝒪} (hz : ‖(z : K)‖ < 1) (hw : ‖(w : K)‖ < 1)
    (h : Lubin.padd (formalGroup (shortO a b)) z w = w) : z = 0 := by
  have e : Lubin.padd (formalGroup (shortO a b)) (Lubin.padd (formalGroup (shortO a b)) z w) (-w) = Lubin.padd (formalGroup (shortO a b)) z (Lubin.padd (formalGroup (shortO a b)) w (-w)) :=
    Lubin.padd_assoc (tn_of_norm hz) (tn_of_norm hw) (tn_of_norm (norm_neg_lt hw))
      (tn_of_norm (norm_padd_lt a b hz hw)) (tn_of_norm (norm_padd_lt a b hw (norm_neg_lt hw)))
  rw [h, padd_neg a b hw, Lubin.padd_zero (tn_of_norm hz)] at e
  exact e.symm

lemma nm_ne_zero {p : ℕ} (hp : p.Prime) {x : 𝒪} (hx : ‖(x : K)‖ < 1) (hx0 : x ≠ 0)
    (hpx : nm a b x p = 0) {d : ℕ} (hd0 : 0 < d) (hdp : d < p) : nm a b x d ≠ 0 := by
  intro hd
  have hcop : Nat.Coprime d p :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt hd0 hdp))
  obtain ⟨m, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have h1 := nm_mul a b x hx hd m
  rw [nm_mod a b hx hpx, hm.2, nm_one a b x hx] at h1
  exact hx0 h1

lemma nm_injOn {p : ℕ} (hp : p.Prime) {x : 𝒪} (hx : ‖(x : K)‖ < 1) (hx0 : x ≠ 0)
    (hpx : nm a b x p = 0) : Set.InjOn (nm a b x) (Set.Iio p) := by
  have aux : ∀ i j, i < j → j < p → nm a b x i = nm a b x j → False := by
    intro i j hij hjp h
    have e : nm a b x j = Lubin.padd (formalGroup (shortO a b)) (nm a b x (j - i)) (nm a b x j) := by
      conv_lhs => rw [show j = (j - i) + i by omega]
      rw [nm_add a b x hx, h]
    exact nm_ne_zero a b hp hx hx0 hpx (d := j - i) (by omega) (by omega)
      (padd_eq_self a b (norm_nm a b x hx _) (norm_nm a b x hx _) e.symm)
  intro i hi j hj h
  rcases lt_trichotomy i j with hl | rfl | hl
  · exact (aux i j hl hj h).elim
  · rfl
  · exact (aux j i hl hi h.symm).elim

/-! ### The cyclic subgroup `⟨x⟩` -/

/-- **the cyclic subgroup** `⟨x⟩ = {[k]x : k < p}` of `F[p]`. -/
noncomputable def cyc {p : ℕ} (hp : p.Prime) {x : 𝒪} (hx : ‖(x : K)‖ < 1) (hpx : nm a b x p = 0) :
    Lubin.FinSub (formalGroup (shortO a b)) where
  H := (Finset.range p).image (nm a b x)
  tn := by
    intro h hh
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hh
    exact tn_of_norm (norm_nm a b x hx k)
  zero_mem := Finset.mem_image.2 ⟨0, Finset.mem_range.2 hp.pos, nm_zero a b x hx⟩
  add_mem := by
    intro u hu v hv
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hv
    rw [← nm_add a b x hx, nm_mod a b hx hpx]
    exact Finset.mem_image.2 ⟨_, Finset.mem_range.2 (Nat.mod_lt _ hp.pos), rfl⟩
  neg_mem := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hu
    refine ⟨nm a b x (p - i), ?_, ?_⟩
    · rw [nm_mod a b hx hpx]
      exact Finset.mem_image.2 ⟨_, Finset.mem_range.2 (Nat.mod_lt _ hp.pos), rfl⟩
    · rw [← nm_add a b x hx, show i + (p - i) = p by have := Finset.mem_range.1 hi; omega, hpx]

lemma card_cyc {p : ℕ} (hp : p.Prime) {x : 𝒪} (hx : ‖(x : K)‖ < 1) (hx0 : x ≠ 0)
    (hpx : nm a b x p = 0) : (cyc a b hp hx hpx).H.card = p := by
  show ((Finset.range p).image (nm a b x)).card = p
  rw [Finset.card_image_of_injOn, Finset.card_range]
  rw [Finset.coe_range]
  exact nm_injOn a b hp hx hx0 hpx

lemma cyc_tors {p : ℕ} (hp : p.Prime) {x : 𝒪} (hx : ‖(x : K)‖ < 1) (hpx : nm a b x p = 0) :
    ∀ h ∈ (cyc a b hp hx hpx).H, nm a b h p = 0 := by
  intro h hh
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hh
  rw [nm_nm a b hx, mul_comm, nm_mul a b x hx hpx]

lemma mem_cyc {p : ℕ} (hp : p.Prime) {x : 𝒪} (hx : ‖(x : K)‖ < 1) (hpx : nm a b x p = 0) :
    x ∈ (cyc a b hp hx hpx).H :=
  Finset.mem_image.2 ⟨1, Finset.mem_range.2 hp.one_lt, nm_one a b x hx⟩

lemma nm_mem (C : Lubin.FinSub (formalGroup (shortO a b))) {x : 𝒪} (hx : x ∈ C.H) (n : ℕ) : nm a b x n ∈ C.H := by
  have hx1 : ‖(x : K)‖ < 1 := VeluLubin.norm_lt_one_of_tn (C.tn x hx)
  induction n with
  | zero => rw [nm_zero a b x hx1]; exact C.zero_mem
  | succ n ih => rw [nm_succ a b x hx1]; exact C.add_mem _ hx _ ih

/-- **an order-`p` subgroup is generated by any nonzero point of it.** -/
lemma eq_cyc {p : ℕ} (hp : p.Prime) (C : Lubin.FinSub (formalGroup (shortO a b))) (hcard : C.H.card = p) {x : 𝒪}
    (hxC : x ∈ C.H) (hx0 : x ≠ 0) (hpx : nm a b x p = 0) :
    C.H = (cyc a b hp (VeluLubin.norm_lt_one_of_tn (C.tn x hxC)) hpx).H := by
  have hx1 : ‖(x : K)‖ < 1 := VeluLubin.norm_lt_one_of_tn (C.tn x hxC)
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro h hh
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hh
    exact nm_mem a b C hxC k
  · rw [hcard, card_cyc a b hp hx1 hx0 hpx]

end Mult

/-! ### `T` as a subgroup, and `Pt : T ≅ E(K)[p]` -/

section PtT
variable [CharZero K] [DecidableEq K] (a b : ↥(CanonicalIsogeny.integers K))

/-- the torsion set as a `FinSub`. -/
noncomputable def torsSub (p : ℕ) (T : Finset 𝒪)
    (hT : ∀ z, z ∈ T ↔ ‖(z : K)‖ < 1 ∧ nm a b z p = 0) : Lubin.FinSub (formalGroup (shortO a b)) where
  H := T
  tn := fun h hh => tn_of_norm ((hT h).1 hh).1
  zero_mem := (hT 0).2 ⟨by simp, nm_of_zero a b p⟩
  add_mem := fun u hu v hv => by
    obtain ⟨hu1, hu2⟩ := (hT u).1 hu
    obtain ⟨hv1, hv2⟩ := (hT v).1 hv
    exact (hT _).2 ⟨norm_padd_lt a b hu1 hv1, by
      rw [nm_padd a b hu1 hv1, hu2, hv2, Lubin.padd_zero Lubin.tn0]⟩
  neg_mem := fun u hu => by
    obtain ⟨hu1, hu2⟩ := (hT u).1 hu
    refine ⟨-u, (hT _).2 ⟨norm_neg_lt hu1, ?_⟩, padd_neg a b hu1⟩
    have e := nm_padd a b hu1 (norm_neg_lt hu1) p
    rw [padd_neg a b hu1, nm_of_zero, hu2,
      Lubin.zero_padd (tn_of_norm (norm_nm a b _ (norm_neg_lt hu1) p))] at e
    exact e.symm


lemma Pt_nm {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {T : Finset 𝒪}
    (hT : ∀ z, z ∈ T ↔ ‖(z : K)‖ < 1 ∧ nm a b z p = 0) {x : 𝒪} (hx : x ∈ T) (k : ℕ) : Pt a b (nm a b x k) = k • Pt a b x := by
  have hx1 := ((hT x).1 hx).1
  have hpS : ∀ h ∈ (torsSub a b p T hT).H, nm a b h p = 0 := fun h hh => ((hT h).1 hh).2
  have hmem : ∀ k, nm a b x k ∈ T := fun k => nm_mem a b (torsSub a b p T hT) hx k
  induction k with
  | zero => rw [nm_zero a b x hx1, Pt_zero, zero_nsmul]
  | succ k ih =>
    rw [nm_succ a b x hx1, Pt_hom a b hp hp5 (torsSub a b p T hT) hpS hx (hmem k), ih, succ_nsmul,
      add_comm]

lemma Pt_tors {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {T : Finset 𝒪}
    (hT : ∀ z, z ∈ T ↔ ‖(z : K)‖ < 1 ∧ nm a b z p = 0) {x : 𝒪} (hx : x ∈ T) : p • Pt a b x = 0 := by
  rw [← Pt_nm a b hp hp5 hT hx p, ((hT x).1 hx).2, Pt_zero]

lemma Pt_injOn {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {T : Finset 𝒪}
    (hT : ∀ z, z ∈ T ↔ ‖(z : K)‖ < 1 ∧ nm a b z p = 0) : Set.InjOn (Pt a b) (T : Set 𝒪) := by
  intro x hx y hy hxy
  have hx1 := ((hT x).1 hx).1
  have hy1 := ((hT y).1 hy).1
  have hpS : ∀ h ∈ (torsSub a b p T hT).H, nm a b h p = 0 := fun h hh => ((hT h).1 hh).2
  have hny : -y ∈ T := (hT _).2 ⟨norm_neg_lt hy1, by
    obtain ⟨z, hz, hz0⟩ := (torsSub a b p T hT).neg_mem y hy
    have := padd_cancel a b hy1 (VeluLubin.norm_lt_one_of_tn ((torsSub a b p T hT).tn z hz)) hz0
    rw [← this]; exact ((hT z).1 hz).2⟩
  have e := Pt_hom a b hp hp5 (torsSub a b p T hT) hpS (x := x) (y := -y) hx hny
  rw [Pt_neg, hxy, add_neg_cancel] at e
  have h0 : Lubin.padd (formalGroup (shortO a b)) x (-y) = 0 := by
    by_contra hne
    exact Pt_ne_zero a b hne (norm_padd_lt a b hx1 (norm_neg_lt hy1)) e
  have := padd_cancel a b hx1 (norm_neg_lt hy1) h0
  exact (neg_inj.1 this).symm

/-- **`Pt(T) = E(K)[p]`**. -/
lemma Pt_surj [IsAlgClosed K] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {T : Finset 𝒪}
    (hT : ∀ z, z ∈ T ↔ ‖(z : K)‖ < 1 ∧ nm a b z p = 0) (hTc : T.card = p ^ 2)
    (hΔ' : 4 * (a : K) ^ 3 + 27 * (b : K) ^ 2 ≠ 0) {P : (Velu.short (a : K) (b : K)).Point}
    (hP : p • P = 0) : ∃ z ∈ T, Pt a b z = P := by
  classical
  obtain ⟨T', hT', hT'c⟩ := TorsionSpec.fullTorsion (F := K) hp.two_le (a : K) (b : K) hΔ'
  have hsub : T.image (Pt a b) ⊆ T' := by
    intro Q hQ
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hQ
    exact (hT' _).2 (Pt_tors a b hp hp5 hT hz)
  have hc : T'.card ≤ (T.image (Pt a b)).card := by
    rw [Finset.card_image_of_injOn (Pt_injOn a b hp hp5 hT), hTc, hT'c]
  have heq := Finset.eq_of_subset_of_card_le hsub hc
  have : P ∈ T.image (Pt a b) := heq ▸ (hT' P).2 hP
  obtain ⟨z, hz, hzP⟩ := Finset.mem_image.1 this
  exact ⟨z, hz, hzP⟩

lemma neg_mem_T {p : ℕ} {T : Finset 𝒪} (hT : ∀ z, z ∈ T ↔ ‖(z : K)‖ < 1 ∧ nm a b z p = 0)
    {x : 𝒪} (hx : x ∈ T) : -x ∈ T := by
  have hx1 := ((hT x).1 hx).1
  refine (hT _).2 ⟨norm_neg_lt hx1, ?_⟩
  obtain ⟨z, hz, hz0⟩ := (torsSub a b p T hT).neg_mem x hx
  have := padd_cancel a b hx1 (VeluLubin.norm_lt_one_of_tn ((torsSub a b p T hT).tn z hz)) hz0
  rw [← this]; exact ((hT z).1 hz).2

/-- the image under `Pt` of a `FinSub` inside `T` is a subgroup of `E(K)`. -/
lemma isSub_image {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {T : Finset 𝒪}
    (hT : ∀ z, z ∈ T ↔ ‖(z : K)‖ < 1 ∧ nm a b z p = 0) (C : Lubin.FinSub (formalGroup (shortO a b))) (hCT : C.H ⊆ T) :
    SubgroupSum.IsSub (C.H.image (Pt a b)) := by
  classical
  have hpS : ∀ h ∈ (torsSub a b p T hT).H, nm a b h p = 0 := fun h hh => ((hT h).1 hh).2
  refine ⟨Finset.mem_image.2 ⟨0, C.zero_mem, Pt_zero a b⟩, ?_, ?_⟩
  · intro P hP Q hQ
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hP
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hQ
    exact Finset.mem_image.2 ⟨_, C.add_mem u hu v hv,
      Pt_hom a b hp hp5 (torsSub a b p T hT) hpS (hCT hu) (hCT hv)⟩
  · intro P hP
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hP
    obtain ⟨w, hw, hw0⟩ := C.neg_mem u hu
    have hu1 := ((hT u).1 (hCT hu)).1
    have := padd_cancel a b hu1 (VeluLubin.norm_lt_one_of_tn (C.tn w hw)) hw0
    exact Finset.mem_image.2 ⟨w, hw, by rw [this, Pt_neg]⟩

/-- an order-`p` `FinSub` inside `T` gives an order-`p` subgroup of `E(K)`. -/
lemma image_mem_subs {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {T : Finset 𝒪}
    (hT : ∀ z, z ∈ T ↔ ‖(z : K)‖ < 1 ∧ nm a b z p = 0) (C : Lubin.FinSub (formalGroup (shortO a b))) (hCT : C.H ⊆ T)
    (hcard : C.H.card = p) :
    C.H.image (Pt a b) ∈ SubgroupSum.subs (a : K) (b : K) p := by
  classical
  refine ⟨isSub_image a b hp hp5 hT C hCT, ?_⟩
  rw [Finset.card_image_of_injOn ((Pt_injOn a b hp hp5 hT).mono (by exact_mod_cast hCT)), hcard]

/-- the `FinSub` of `T` lying over a subgroup `G ⊂ E(K)`. -/
noncomputable def ofSub {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {T : Finset 𝒪}
    (hT : ∀ z, z ∈ T ↔ ‖(z : K)‖ < 1 ∧ nm a b z p = 0)
    {G : Finset (Velu.short (a : K) (b : K)).Point} (hG : SubgroupSum.IsSub G) :
    Lubin.FinSub (formalGroup (shortO a b)) where
  H := T.filter (fun z => Pt a b z ∈ G)
  tn := fun h hh => (torsSub a b p T hT).tn h (Finset.mem_filter.1 hh).1
  zero_mem := Finset.mem_filter.2 ⟨(torsSub a b p T hT).zero_mem, by rw [Pt_zero]; exact hG.1⟩
  add_mem := fun u hu v hv => by
    obtain ⟨hu1, hu2⟩ := Finset.mem_filter.1 hu
    obtain ⟨hv1, hv2⟩ := Finset.mem_filter.1 hv
    refine Finset.mem_filter.2 ⟨(torsSub a b p T hT).add_mem u hu1 v hv1, ?_⟩
    rw [Pt_hom a b hp hp5 (torsSub a b p T hT) (fun h hh => ((hT h).1 hh).2) hu1 hv1]
    exact hG.2.1 _ hu2 _ hv2
  neg_mem := fun u hu => by
    obtain ⟨hu1, hu2⟩ := Finset.mem_filter.1 hu
    refine ⟨-u, Finset.mem_filter.2 ⟨neg_mem_T a b hT hu1, ?_⟩,
      padd_neg a b ((hT u).1 hu1).1⟩
    rw [Pt_neg]; exact hG.2.2 _ hu2

lemma ofSub_sub {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {T : Finset 𝒪}
    (hT : ∀ z, z ∈ T ↔ ‖(z : K)‖ < 1 ∧ nm a b z p = 0)
    {G : Finset (Velu.short (a : K) (b : K)).Point} (hG : SubgroupSum.IsSub G) :
    (ofSub a b hp hp5 hT hG).H ⊆ T := Finset.filter_subset _ _

/-- **`Pt(ofSub G) = G`** for every order-`p` subgroup `G ⊂ E(K)`. -/
lemma image_ofSub [IsAlgClosed K] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {T : Finset 𝒪}
    (hT : ∀ z, z ∈ T ↔ ‖(z : K)‖ < 1 ∧ nm a b z p = 0) (hTc : T.card = p ^ 2)
    (hΔ' : 4 * (a : K) ^ 3 + 27 * (b : K) ^ 2 ≠ 0)
    {G : Finset (Velu.short (a : K) (b : K)).Point} (hG : G ∈ SubgroupSum.subs (a : K) (b : K) p) :
    (ofSub a b hp hp5 hT hG.1).H.image (Pt a b) = G := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  ext P
  constructor
  · intro hP
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hP
    exact (Finset.mem_filter.1 hz).2
  · intro hP
    obtain ⟨z, hz, hzP⟩ := Pt_surj a b hp hp5 hT hTc hΔ' (HeckeBridge.nsmul_eq_zero_of_mem_subs hG hP)
    exact Finset.mem_image.2 ⟨z, Finset.mem_filter.2 ⟨hz, hzP ▸ hP⟩, hzP⟩

lemma card_ofSub [IsAlgClosed K] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {T : Finset 𝒪}
    (hT : ∀ z, z ∈ T ↔ ‖(z : K)‖ < 1 ∧ nm a b z p = 0) (hTc : T.card = p ^ 2)
    (hΔ' : 4 * (a : K) ^ 3 + 27 * (b : K) ^ 2 ≠ 0)
    {G : Finset (Velu.short (a : K) (b : K)).Point} (hG : G ∈ SubgroupSum.subs (a : K) (b : K) p) :
    (ofSub a b hp hp5 hT hG.1).H.card = p := by
  classical
  have h := image_ofSub a b hp hp5 hT hTc hΔ' hG
  have e := Finset.card_image_of_injOn ((Pt_injOn a b hp hp5 hT).mono
    (by exact_mod_cast ofSub_sub a b hp hp5 hT hG.1))
  have h2 := congrArg Finset.card h
  have h3 := hG.2
  omega

lemma tors_ofSub {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {T : Finset 𝒪}
    (hT : ∀ z, z ∈ T ↔ ‖(z : K)‖ < 1 ∧ nm a b z p = 0)
    {G : Finset (Velu.short (a : K) (b : K)).Point} (hG : SubgroupSum.IsSub G) :
    ∀ h ∈ (ofSub a b hp hp5 hT hG).H, nm a b h p = 0 :=
  fun h hh => ((hT h).1 (ofSub_sub a b hp hp5 hT hG hh)).2

end PtT

end AllQuotients
