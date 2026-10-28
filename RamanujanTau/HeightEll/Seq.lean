/-
# The universal `x`-coordinate sequence `Xₙ ∈ k(t)` and its height bound

`X₁ = t`, `X₂ = kPhi(t)/kPsi(t)`, `X_{n+3} = kS(X_{n+2}, t)/(X_{n+2} - t)² - X_{n+1}`.
For any field `L ⊇ k` (via `j`), any point `Q` of `W(L)` whose `x`-coordinate `ξ` is transcendental
over `k`, and `N` with `m • Q ≠ 0` for `1 ≤ m ≤ N`: `x(n • Q) = Xₙ(ξ)` for `1 ≤ n ≤ N`, and the
heights satisfy `ht Xₙ ≤ n²`.
-/
import RamanujanTau.HeightEll.Kummer
import RamanujanTau.HeightEll.Gauss

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace HeightEll

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

section Maps
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (V : WeierstrassCurve R)

lemma map_kS (x y : R) : f (kS V x y) = kS (V.map f) (f x) (f y) := by
  simp [kS, map_ofNat]
lemma map_kQ (x y : R) : f (kQ V x y) = kQ (V.map f) (f x) (f y) := by
  simp [kQ]
lemma map_kPsi (x : R) : f (kPsi V x) = kPsi (V.map f) (f x) := by
  simp [kPsi, map_ofNat]
lemma map_kPhi (x : R) : f (kPhi V x) = kPhi (V.map f) (f x) := by
  simp [kPhi, map_ofNat]

/-- homogenised numerators. -/
def kSh (c d t : R) : R :=
  2 * c * t * (c + t * d) + V.b₂ * c * t * d + V.b₄ * (c * d + t * d ^ 2) + V.b₆ * d ^ 2
def kQh (c d t : R) : R :=
  c ^ 2 * t ^ 2 - V.b₄ * c * t * d - V.b₆ * (c * d + t * d ^ 2) - V.b₈ * d ^ 2

lemma map_kSh (c d t : R) : f (kSh V c d t) = kSh (V.map f) (f c) (f d) (f t) := by
  simp [kSh, map_ofNat]
lemma map_kQh (c d t : R) : f (kQh V c d t) = kQh (V.map f) (f c) (f d) (f t) := by
  simp [kQh]

end Maps

lemma kS_homog {F : Type*} [Field F] (V : WeierstrassCurve F) {c d : F} (hd : d ≠ 0) (t : F) :
    d ^ 2 * kS V (c / d) t = kSh V c d t := by
  simp only [kS, kSh]; field_simp
lemma kQ_homog {F : Type*} [Field F] (V : WeierstrassCurve F) {c d : F} (hd : d ≠ 0) (t : F) :
    d ^ 2 * kQ V (c / d) t = kQh V c d t := by
  simp only [kQ, kQh]; field_simp

section Deg
variable {k : Type*} [Field k]

lemma nd_mul {a b : k[X]} {i j : ℕ} (ha : a.natDegree ≤ i) (hb : b.natDegree ≤ j) :
    (a * b).natDegree ≤ i + j := natDegree_mul_le.trans (add_le_add ha hb)
lemma nd_add {a b : k[X]} {i : ℕ} (ha : a.natDegree ≤ i) (hb : b.natDegree ≤ i) :
    (a + b).natDegree ≤ i := (natDegree_add_le _ _).trans (max_le ha hb)
lemma nd_sub {a b : k[X]} {i : ℕ} (ha : a.natDegree ≤ i) (hb : b.natDegree ≤ i) :
    (a - b).natDegree ≤ i := (natDegree_sub_le _ _).trans (max_le ha hb)
lemma nd_C (r : k) : (C r).natDegree ≤ 0 := by simp
lemma nd_ofNat (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : k[X]).natDegree ≤ 0 := by
  rw [natDegree_ofNat]
lemma nd_X : (X : k[X]).natDegree ≤ 1 := natDegree_X_le
lemma nd_mono {a : k[X]} {i j : ℕ} (ha : a.natDegree ≤ i) (h : i ≤ j) : a.natDegree ≤ j := ha.trans h

variable (W : WeierstrassCurve k)

lemma nd_add2 {a b : k[X]} {i j : ℕ} (ha : a.natDegree ≤ i) (hb : b.natDegree ≤ j) :
    (a + b).natDegree ≤ max i j := (natDegree_add_le _ _).trans (max_le_max ha hb)
lemma nd_sub2 {a b : k[X]} {i j : ℕ} (ha : a.natDegree ≤ i) (hb : b.natDegree ≤ j) :
    (a - b).natDegree ≤ max i j := (natDegree_sub_le _ _).trans (max_le_max ha hb)

lemma nd_kSh {c d : k[X]} {h : ℕ} (hc : c.natDegree ≤ h) (hd : d.natDegree ≤ h) :
    (kSh (W.map C) c d X).natDegree ≤ 2 * h + 2 := by
  simp only [kSh, map_b₂, map_b₄, map_b₆, pow_two]
  refine nd_mono (nd_add2 (nd_add2 (nd_add2
    (nd_mul (nd_mul (nd_mul (nd_ofNat 2) hc) nd_X) (nd_add2 hc (nd_mul nd_X hd)))
    (nd_mul (nd_mul (nd_mul (nd_C _) hc) nd_X) hd))
    (nd_mul (nd_C _) (nd_add2 (nd_mul hc hd) (nd_mul nd_X (nd_mul hd hd)))))
    (nd_mul (nd_C _) (nd_mul hd hd))) ?_
  omega

lemma nd_kQh {c d : k[X]} {h : ℕ} (hc : c.natDegree ≤ h) (hd : d.natDegree ≤ h) :
    (kQh (W.map C) c d X).natDegree ≤ 2 * h + 2 := by
  simp only [kQh, map_b₄, map_b₆, map_b₈, pow_two]
  refine nd_mono (nd_sub2 (nd_sub2 (nd_sub2
    (nd_mul (nd_mul hc hc) (nd_mul nd_X nd_X))
    (nd_mul (nd_mul (nd_mul (nd_C _) hc) nd_X) hd))
    (nd_mul (nd_C _) (nd_add2 (nd_mul hc hd) (nd_mul nd_X (nd_mul hd hd)))))
    (nd_mul (nd_C _) (nd_mul hd hd))) ?_
  omega

lemma nd_E {c d : k[X]} {h : ℕ} (hc : c.natDegree ≤ h) (hd : d.natDegree ≤ h) :
    ((c - X * d) ^ 2).natDegree ≤ 2 * h + 2 := by
  rw [pow_two]
  refine nd_mono (nd_mul (nd_sub2 hc (nd_mul nd_X hd)) (nd_sub2 hc (nd_mul nd_X hd))) ?_
  omega

end Deg

/-! ## The sequence -/

variable {k : Type*} [Field k] (W : WeierstrassCurve k)

/-- `k[X] → k(X)`. -/
noncomputable abbrev ιk : k[X] →+* RatFunc k := algebraMap k[X] (RatFunc k)

/-- the curve over `k(t)`. -/
noncomputable abbrev Wr : WeierstrassCurve (RatFunc k) := W.map ((ιk (k := k)).comp C)

/-- the variable `t`. -/
noncomputable abbrev tX : RatFunc k := ιk (k := k) X

lemma Wr_eq : Wr W = (W.map C).map (ιk (k := k)) := by rw [WeierstrassCurve.map_map]

/-- **the universal `x`-coordinates** `Xₙ ∈ k(t)`. -/
noncomputable def Xs : ℕ → RatFunc k
  | 0 => 0
  | 1 => tX
  | 2 => kPhi (Wr W) tX / kPsi (Wr W) tX
  | (n + 3) => kS (Wr W) (Xs (n + 2)) tX / (Xs (n + 2) - tX) ^ 2 - Xs (n + 1)

section NS
variable {L : Type*} [Field L] [DecidableEq L] (j : k →+* L)

lemma xc_ne_of_nsmul {Q : (W.map j).toAffine.Point} {m : ℕ} (hm1 : (m + 1) • Q ≠ 0)
    (hm3 : (m + 3) • Q ≠ 0) (hA : (m + 2) • Q ≠ 0) (hQ : Q ≠ 0) :
    xc _ ((m + 2) • Q) ≠ xc _ Q := by
  intro h
  rcases eq_or_eq_neg_of_xc_eq _ hA hQ h with h | h
  · apply hm1
    have e : (m + 1) • Q + Q = Q := by rw [← succ_nsmul]; exact h
    have := congrArg (· - Q) e
    simpa using this
  · apply hm3
    rw [succ_nsmul, h, neg_add_cancel]

end NS

section Eval
variable {L : Type*} [Field L] (j : k →+* L) (ξ : L)
  (hξ : ∀ A : k[X], A ≠ 0 → A.eval₂ j ξ ≠ 0)
include hξ

/-- evaluation `t ↦ ξ`. -/
noncomputable def evr : RatFunc k →+* L :=
  RatFunc.liftRingHom (eval₂RingHom j ξ) (fun A hA => by
    rw [mem_nonZeroDivisors_iff_ne_zero] at hA
    rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
    exact hξ A hA)

lemma evr_alg (A : k[X]) : evr j ξ hξ (ιk A) = A.eval₂ j ξ := by
  simp [evr]

lemma evr_tX : evr j ξ hξ tX = ξ := by rw [evr_alg]; simp

lemma Wr_map : (Wr W).map (evr j ξ hξ) = W.map j := by
  rw [WeierstrassCurve.map_map]; congr 1; ext c
  show evr j ξ hξ (ιk (C c)) = j c
  rw [evr_alg, eval₂_C]

variable [DecidableEq L]

/-- **universality**: `x(n • Q) = Xₙ(ξ)`. -/
theorem xc_nsmul (Q : (W.map j).toAffine.Point) (hQx : xc _ Q = ξ) (N : ℕ)
    (hN : ∀ m, 1 ≤ m → m ≤ N → m • Q ≠ 0) :
    ∀ n, 1 ≤ n → n ≤ N → xc _ (n • Q) = evr j ξ hξ (Xs W n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn hnN
  have hQ : Q ≠ 0 := by simpa using hN 1 le_rfl (by omega)
  obtain ⟨x₀, y₀, h₀, rfl⟩ := eq_some_of_ne_zero _ hQ
  simp only [xc_some] at hQx
  subst hQx
  match n, hn with
  | 1, _ => rw [one_nsmul, xc_some]; exact (evr_tX j x₀ hξ).symm
  | 2, _ =>
    have h2 := hN 2 (by omega) hnN
    rw [two_nsmul] at h2 ⊢
    obtain ⟨hp, hd⟩ := doubling _ h₀ h2
    simp only [Xs, map_div₀, map_kPhi, map_kPsi, Wr_map, evr_tX]
    rw [eq_div_iff hp, mul_comm, hd]
  | m + 3, _ =>
    have hA := hN (m + 2) (by omega) (by omega)
    have hx := xc_ne_of_nsmul W j (hN (m + 1) (by omega) (by omega)) (hN (m + 3) (by omega) hnN) hA hQ
    have ih2 := ih (m + 2) (by omega) (by omega) (by omega)
    have ih1 := ih (m + 1) (by omega) (by omega) (by omega)
    obtain ⟨x₁, y₁, h₁, hA1⟩ := eq_some_of_ne_zero _ hA
    rw [hA1, xc_some] at hx ih2
    have hk := (kummer _ h₁ h₀ hx).2.2.1
    rw [← hA1, ← succ_nsmul, show (m + 2) • Point.some x₀ y₀ h₀ - Point.some x₀ y₀ h₀ =
      (m + 1) • Point.some x₀ y₀ h₀ by
        rw [show m + 2 = (m + 1) + 1 from rfl, succ_nsmul, add_sub_cancel_right]] at hk
    rw [ih1] at hk
    have hd : (x₁ - x₀) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.2 hx)
    simp only [Xs, map_sub, map_div₀, map_pow, map_kS, Wr_map, evr_tX, ← ih2]
    rw [eq_sub_iff_add_eq, eq_div_iff hd, mul_comm, hk]

/-- the Kummer relations transported to `k(t)`. -/
theorem Xs_rel (Q : (W.map j).toAffine.Point) (hQx : xc _ Q = ξ) (N : ℕ)
    (hN : ∀ m, 1 ≤ m → m ≤ N → m • Q ≠ 0) (m : ℕ) (hm : m + 3 ≤ N) :
    Xs W (m + 2) ≠ tX ∧ (Xs W (m + 2) - tX) ^ 2 * (Xs W (m + 3) * Xs W (m + 1)) =
      kQ (Wr W) (Xs W (m + 2)) tX := by
  have hU := xc_nsmul W j ξ hξ Q hQx N hN
  have hQ : Q ≠ 0 := by simpa using hN 1 le_rfl (by omega)
  have hA := hN (m + 2) (by omega) (by omega)
  have hx := xc_ne_of_nsmul W j (hN (m + 1) (by omega) (by omega)) (hN (m + 3) (by omega) hm) hA hQ
  obtain ⟨x₀, y₀, h₀, rfl⟩ := eq_some_of_ne_zero _ hQ
  obtain ⟨x₁, y₁, h₁, hA1⟩ := eq_some_of_ne_zero _ hA
  simp only [xc_some] at hQx
  have e2 := hU (m + 2) (by omega) (by omega)
  have e3 := hU (m + 3) (by omega) hm
  have e1 := hU (m + 1) (by omega) (by omega)
  rw [hA1, xc_some] at hx e2
  rw [xc_some] at hx
  have hk := (kummer _ h₁ h₀ hx).2.2.2
  rw [← hA1, ← succ_nsmul, show (m + 2) • Point.some x₀ y₀ h₀ - Point.some x₀ y₀ h₀ =
    (m + 1) • Point.some x₀ y₀ h₀ by
      rw [show m + 2 = (m + 1) + 1 from rfl, succ_nsmul, add_sub_cancel_right]] at hk
  rw [e3, e1, e2, hQx] at hk
  refine ⟨fun h => hx (by rw [e2, hQx, h, evr_tX]), ?_⟩
  apply (evr j ξ hξ).injective
  simp only [map_mul, map_pow, map_sub, map_kQ, Wr_map, evr_tX]
  exact hk

lemma kPsi_ne (Q : (W.map j).toAffine.Point) (hQx : xc _ Q = ξ) (h2 : 2 • Q ≠ 0) (hQ : Q ≠ 0) :
    kPsi (Wr W) tX ≠ 0 := by
  obtain ⟨x₀, y₀, h₀, rfl⟩ := eq_some_of_ne_zero _ hQ
  simp only [xc_some] at hQx
  rw [two_nsmul] at h2
  intro h
  have := (doubling _ h₀ h2).1
  apply this
  have e := congrArg (evr j ξ hξ) h
  rwa [map_kPsi, Wr_map, evr_tX, map_zero, ← hQx] at e

/-- **the height bound** `ht Xₙ ≤ n²`. -/
theorem ht_Xs_le (Q : (W.map j).toAffine.Point) (hQx : xc _ Q = ξ) (N : ℕ) (hN2 : 2 ≤ N)
    (hN : ∀ m, 1 ≤ m → m ≤ N → m • Q ≠ 0) :
    ∀ n, 1 ≤ n → n ≤ N → ht (Xs W n) ≤ n ^ 2 := by
  apply telescope (fun n => ht (Xs W n)) N
  · show ht tX = 1
    simp [ht]
  · show ht (kPhi (Wr W) tX / kPsi (Wr W) tX) ≤ 4
    have hQ : Q ≠ 0 := by simpa using hN 1 le_rfl (by omega)
    have hp := kPsi_ne W j ξ hξ Q hQx (hN 2 (by omega) hN2) hQ
    rw [Wr_eq, ← map_kPsi] at hp
    rw [Wr_eq, ← map_kPhi, ← map_kPsi]
    have hp' : kPsi (W.map C) (X : k[X]) ≠ 0 := by rintro h; rw [h, map_zero] at hp; exact hp rfl
    apply ht_le_of_eq_div hp' rfl
    · simp only [kPhi, map_b₄, map_b₆, map_b₈]; compute_degree!
    · simp only [kPsi, map_b₂, map_b₄, map_b₆]
      refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le
        ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)) ?_)
      all_goals compute_degree
      all_goals norm_num
  · intro m hm2 hmN
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
    obtain ⟨hne, hrel⟩ := Xs_rel W j ξ hξ Q hQx N hN n (by omega)
    show ht (Xs W (n + 3)) + ht (Xs W (n + 1)) ≤ 2 * ht (Xs W (n + 2)) + 2
    set x := Xs W (n + 2)
    set c := x.num
    set d := x.denom
    have hd : d ≠ 0 := RatFunc.denom_ne_zero x
    have hdi : ιk d ≠ 0 := RatFunc.algebraMap_ne_zero hd
    have ex : x = ιk c / ιk d := (RatFunc.num_div_denom x).symm
    have hc : c.natDegree ≤ ht x := le_max_left _ _
    have hd' : d.natDegree ≤ ht x := le_max_right _ _
    have hEi : ιk ((c - X * d) ^ 2) = ιk d ^ 2 * (x - tX) ^ 2 := by
      rw [ex]; simp only [map_pow, map_sub, map_mul]; field_simp
    have hE : (c - X * d) ^ 2 ≠ 0 := by
      intro h; rw [h, map_zero] at hEi
      exact mul_ne_zero (pow_ne_zero 2 hdi) (pow_ne_zero 2 (sub_ne_zero.2 hne)) hEi.symm
    -- the sum relation is the definition
    have hsum : (x - tX) ^ 2 * (Xs W (n + 3) + Xs W (n + 1)) = kS (Wr W) x tX := by
      have hx0 : (x - tX) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.2 hne)
      show (x - tX) ^ 2 * (kS (Wr W) x tX / (x - tX) ^ 2 - Xs W (n + 1) + Xs W (n + 1)) = _
      rw [sub_add_cancel, mul_div_assoc', mul_div_cancel_left₀ _ hx0]
    apply ht_add_ht_le hE (S := kSh (W.map C) c d X) (Q := kQh (W.map C) c d X)
    · have e : ιk d ^ 2 * (x - tX) ^ 2 * (Xs W (n + 3) * Xs W (n + 1)) =
          ιk d ^ 2 * ((x - tX) ^ 2 * (Xs W (n + 3) * Xs W (n + 1))) := by ring
      rw [hEi, e, hrel, map_kQh, ← Wr_eq, ex, kQ_homog _ hdi]
    · have e : ιk d ^ 2 * (x - tX) ^ 2 * (Xs W (n + 3) + Xs W (n + 1)) =
          ιk d ^ 2 * ((x - tX) ^ 2 * (Xs W (n + 3) + Xs W (n + 1))) := by ring
      rw [hEi, e, hsum, map_kSh, ← Wr_eq, ex, kS_homog _ hdi]
    · exact nd_E hc hd'
    · exact nd_kSh W hc hd'
    · exact nd_kQh W hc hd'

end Eval

end HeightEll
