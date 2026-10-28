/-
# Vélu's `Y` at the generic point as a sum over translates

For `h ∈ 𝔪 ∖ 0` with `Q = Pt h`, Vélu's jet identity (`Velu.jet_alg`, `k = 1`) at the generic point
`P(z)` of `E(L)`, `L = Frac K⟦z⟧`, together with `yc_chord`, gives (`pair_identity`)
  `1/w(F(z,h)) + 1/w(F(z,-h)) = -(t_Q r_Q² + 2 u_Q r_Q³)/w(z)`.
Summing over a finite subgroup `S ⊆ 𝔪` whose points form the Vélu kernel `κ` (`κ.G = Pt(S)`):
  `Σ_{h∈S} 1/w(F(z,h)) = Xd/w`   (`sum_inv_wh`),
i.e. `Dser = Xd · Wst` in `K⟦z⟧` (`map_Dser`): the integral series `Dser` is Vélu's `Xd` times
`∏_{h≠0} w(F(z,h))`.
-/
import RamanujanTau.VeluDescent.Chord

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace VeluDescent
open MvPowerSeries EllipticFormal VeluLubin

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [DecidableEq K]

local notation "𝒪" => CanonicalIsogeny.integers K
local notation "jK" => Subring.subtype (CanonicalIsogeny.integers K)
local notation "LL" => FractionRing (MvPowerSeries Unit K)
local notation "iL" => algebraMap (MvPowerSeries Unit K) (FractionRing (MvPowerSeries Unit K))

variable {a b : ↥(CanonicalIsogeny.integers K)}

lemma equation_Pt {h : 𝒪} (h0 : h ≠ 0) (hh : ‖(h : K)‖ < 1) :
    (jj (Velu.yc (Pt a b h)) : LL) ^ 2 =
      jj (Velu.xc (Pt a b h)) ^ 3 + jj (a : K) * jj (Velu.xc (Pt a b h)) + jj (b : K) := by
  have e := Velu.equation_xc_yc (Pt_ne_zero a b h0 hh)
  have e2 := congrArg (jj (K := K)) e
  rw [map_pow, map_add, map_add, map_mul, map_pow] at e2
  exact e2

/-- the algebra behind `pair_identity`, in an abstract field. -/
lemma pair_alg {F : Type*} [Field F] {x0 y0 xq yq c W1 W2 r A : F} (hc : c ≠ 0) (hy0 : y0 = -1 / c)
    (hxr : (x0 - xq) * r = 1) (hW1 : W1 ≠ 0) (hW2 : W2 ≠ 0) (hy : y0 ≠ 0)
    (hj : (-1) ^ 1 * ((6 * xq ^ 2 + 2 * A) / (x0 - xq) ^ (1 + 1) +
      (((1 : ℕ) : F) + 1) * (4 * yq ^ 2) / (x0 - xq) ^ (1 + 2)) = -1 / W1 / y0 + -1 / W2 / y0) :
    1 / W1 + 1 / W2 = -((6 * xq ^ 2 + 2 * A) * r ^ 2 + 2 * (4 * yq ^ 2) * r ^ 3) / c := by
  have hd : x0 - xq ≠ 0 := by intro e; rw [e, zero_mul] at hxr; exact zero_ne_one hxr
  have hr : r = 1 / (x0 - xq) := by field_simp; linear_combination hxr
  subst hr hy0
  push_cast at hj
  field_simp at hj ⊢
  linear_combination -hj

/-- **the pair identity**. -/
theorem pair_identity {h : 𝒪} (h0 : h ≠ 0) (hh : ‖(h : K)‖ < 1) :
    1 / iL (MvPowerSeries.map jK (wh a b h)) + 1 / iL (MvPowerSeries.map jK (wh a b (-h))) =
      -(iL (C (Velu.Kernel.tQ (Pt a b h)) * rQ (Pt a b h) ^ 2 +
        2 * C (Velu.Kernel.uQ (Pt a b h)) * rQ (Pt a b h) ^ 3)) / iL (ww (a : K) (b : K)) := by
  set Q := Pt a b h with hQ
  have hnh : ‖((-h : 𝒪) : K)‖ < 1 := norm_neg_lt hh
  have e1 := yc_chord (a := a) (b := b) h0 hh
  have e2 := yc_chord (a := a) (b := b) (neg_ne_zero.2 h0) hnh
  rw [Pt_neg, Velu.xc_neg, Velu.yc_neg, map_neg, ← hQ] at e2
  set x0 : LL := xL (a : K) (b : K)
  set y0 : LL := -1 / iL (ww (a : K) (b : K)) with hy0
  set xq : LL := jj (Velu.xc Q)
  set yq : LL := jj (Velu.yc Q)
  set W1 := iL (MvPowerSeries.map jK (wh a b h))
  set W2 := iL (MvPowerSeries.map jK (wh a b (-h)))
  set r := iL (rQ Q) with hr
  have hw := ι_ww_ne (A := (a : K)) (B := (b : K))
  have hW1 : W1 ≠ 0 := map_wh_ne h0 hh
  have hW2 : W2 ≠ 0 := map_wh_ne (neg_ne_zero.2 h0) hnh
  have hxr : (x0 - xq) * r = 1 := x_sub_mul_r Q
  have hxq : x0 ≠ xq := by
    intro e; rw [e, sub_self, zero_mul] at hxr; exact zero_ne_one hxr
  have hd : x0 - xq ≠ 0 := sub_ne_zero.2 hxq
  have h0e : y0 ^ 2 = x0 ^ 3 + jj (a : K) * x0 + jj (b : K) := by
    rw [f_xL, hy0]; field_simp
  have hy : y0 ≠ 0 := by rw [hy0]; exact div_ne_zero (neg_ne_zero.2 one_ne_zero) hw
  have hj := Velu.jet_alg (jj (a : K)) (jj (b : K)) x0 y0 xq yq h0e (equation_Pt h0 hh) hxq hy
    two_ne_LL 1 (by norm_num)
  simp only [Velu.jet, Velu.cj, one_ne_zero, if_false, sub_zero] at hj
  simp only [chordY, sub_neg_eq_add] at e1 e2
  have e1' : -(((y0 - yq) / (x0 - xq)) * ((((y0 - yq) / (x0 - xq)) ^ 2 - x0 - xq) - x0) + y0) =
      -1 / W1 := e1.symm
  have e2' : -(((y0 + yq) / (x0 - xq)) * ((((y0 + yq) / (x0 - xq)) ^ 2 - x0 - xq) - x0) + y0) =
      -1 / W2 := e2.symm
  rw [e1', e2'] at hj
  have ht : iL (C (Velu.Kernel.tQ Q)) = 6 * xq ^ 2 + 2 * jj (a : K) := by
    rw [← jj_apply, Velu.Kernel.tQ]; simp only [map_add, map_mul, map_pow, map_ofNat, xq]
  have hu : iL (C (Velu.Kernel.uQ Q)) = 4 * yq ^ 2 := by
    rw [← jj_apply, Velu.Kernel.uQ]; simp only [map_mul, map_pow, map_ofNat, yq]
  simp only [map_add, map_mul, map_pow, map_ofNat, ht, hu, ← hr]
  exact pair_alg hw hy0 hxr hW1 hW2 hy hj

/-! ### The subgroup as `{0} ∪ hQ(S) ∪ -hQ(S)` -/

variable (S : Lubin.FinSub (formalGroup (shortO a b)))

lemma neg_mem_H {h : 𝒪} (hh : h ∈ S.H) : -h ∈ S.H := by
  obtain ⟨y, hy, hxy⟩ := S.neg_mem h hh
  have := padd_cancel a b (norm_lt_one_of_tn (S.tn h hh)) (norm_lt_one_of_tn (S.tn y hy)) hxy
  rw [← this]; exact hy

lemma Pt_injOn {x y : 𝒪} (hx : ‖(x : K)‖ < 1) (hy : ‖(y : K)‖ < 1) (h : Pt a b x = Pt a b y) :
    x = y := by
  by_cases hx0 : x = 0
  · subst hx0
    by_contra hy0
    exact Pt_ne_zero a b (Ne.symm hy0) hy (h.symm.trans (Pt_zero a b))
  by_cases hy0 : y = 0
  · subst hy0
    exact absurd (h.trans (Pt_zero a b)) (Pt_ne_zero a b hx0 hx)
  have h1 := congrArg Velu.xc h
  have h2 := congrArg Velu.yc h
  rw [xc_Pt hx0 hx, xc_Pt hy0 hy] at h1
  rw [yc_Pt hx0 hx, yc_Pt hy0 hy] at h2
  have hwx := wz_ne_zero a b hx hx0
  have hwy := wz_ne_zero a b hy hy0
  have hw : (wz a b x : K) = wz a b y := by
    rw [div_eq_div_iff hwx hwy] at h2; linear_combination h2
  rw [hw] at h1
  exact Subtype.ext ((div_left_inj' hwy).1 h1)

variable (κ : Velu.Kernel (a : K) (b : K))
  (hκ : (κ.G : Set (Velu.short (a : K) (b : K)).Point) = Pt a b '' (S.H : Set ↥(CanonicalIsogeny.integers K)))

include hκ

lemma exists_hQ {Q : (Velu.short (a : K) (b : K)).Point} (hQ : Q ∈ κ.S) :
    ∃ h ∈ S.H, Pt a b h = Q := by
  have : Q ∈ (κ.G : Set _) := κ.S_sub hQ
  rw [hκ] at this
  obtain ⟨h, hh, e⟩ := this
  exact ⟨h, hh, e⟩

omit hκ in
/-- a choice of `h ∈ S` with `Pt h = Q`. -/
noncomputable def hQ (Q : (Velu.short (a : K) (b : K)).Point) : 𝒪 := by
  classical exact if hq : ∃ h ∈ S.H, Pt a b h = Q then hq.choose else 0

lemma hQ_spec {Q : (Velu.short (a : K) (b : K)).Point} (hQ' : Q ∈ κ.S) :
    hQ S Q ∈ S.H ∧ Pt a b (hQ S Q) = Q := by
  have hq := exists_hQ S κ hκ hQ'
  rw [hQ, dif_pos hq]
  exact hq.choose_spec

lemma hQ_ne {Q : (Velu.short (a : K) (b : K)).Point} (hQ' : Q ∈ κ.S) : hQ S Q ≠ 0 := by
  intro e
  have := (hQ_spec S κ hκ hQ').2
  rw [e, Pt_zero] at this
  exact κ.zero_not_mem_S (this ▸ hQ')

lemma H_eq : S.H = insert 0 (κ.S.image (hQ S) ∪ κ.S.image (fun Q => -hQ S Q)) := by
  classical
  ext h
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  constructor
  · intro hh
    by_cases h0 : h = 0
    · exact Or.inl h0
    right
    have nh := norm_lt_one_of_tn (S.tn h hh)
    have hG : Pt a b h ∈ κ.G := by
      have : Pt a b h ∈ (κ.G : Set _) := by rw [hκ]; exact ⟨h, hh, rfl⟩
      exact this
    rcases κ.cover _ hG (Pt_ne_zero a b h0 nh) with hS | hS
    · left
      refine ⟨_, hS, ?_⟩
      have := hQ_spec S κ hκ hS
      exact Pt_injOn (norm_lt_one_of_tn (S.tn _ this.1)) nh this.2
    · right
      refine ⟨_, hS, ?_⟩
      have hs := hQ_spec S κ hκ hS
      have e2 : Pt a b (hQ S (-Pt a b h)) = Pt a b (-h) := by rw [Pt_neg]; exact hs.2
      have e := Pt_injOn (norm_lt_one_of_tn (S.tn _ hs.1)) (norm_neg_lt nh) e2
      rw [e, neg_neg]
  · rintro (h0 | ⟨Q, hQ', rfl⟩ | ⟨Q, hQ', rfl⟩)
    · rw [h0]; exact S.zero_mem
    · exact (hQ_spec S κ hκ hQ').1
    · exact neg_mem_H S (hQ_spec S κ hκ hQ').1

/-- `Σ_{h∈S} g h = g 0 + Σ_{Q∈κ.S} (g (hQ Q) + g (-hQ Q))`. -/
lemma sum_H {M : Type*} [AddCommMonoid M] (g : 𝒪 → M) :
    ∑ h ∈ S.H, g h = g 0 + ∑ Q ∈ κ.S, (g (hQ S Q) + g (-hQ S Q)) := by
  classical
  have inj1 : Set.InjOn (hQ S) (κ.S : Set _) := by
    intro Q hQ' Q' hQ'' e
    rw [← (hQ_spec S κ hκ hQ').2, ← (hQ_spec S κ hκ hQ'').2]
    exact congrArg (Pt a b) e
  have inj2 : Set.InjOn (fun Q => -hQ S Q) (κ.S : Set _) := by
    intro Q hQ' Q' hQ'' e
    exact inj1 hQ' hQ'' (neg_injective e)
  rw [H_eq S κ hκ, Finset.sum_insert, Finset.sum_union, Finset.sum_image inj1,
    Finset.sum_image inj2, Finset.sum_add_distrib]
  · rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨Q, hQ', rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨Q', hQ'', e⟩ := Finset.mem_image.1 hx'
    have e' : Pt a b (hQ S Q) = -Pt a b (hQ S Q') := by
      rw [← e, Pt_neg]
    rw [(hQ_spec S κ hκ hQ').2, (hQ_spec S κ hκ hQ'').2] at e'
    exact κ.neg_not_mem_S Q' hQ'' (e' ▸ hQ')
  · simp only [Finset.mem_union, Finset.mem_image, not_or, not_exists, not_and]
    refine ⟨fun Q hQ' e => hQ_ne S κ hκ hQ' e, fun Q hQ' e => hQ_ne S κ hκ hQ' (neg_eq_zero.1 e)⟩

/-- **`Σ_{h∈S} 1/w(F(z,h)) = Xd/w`**. -/
theorem sum_inv_wh :
    ∑ h ∈ S.H, 1 / iL (MvPowerSeries.map jK (wh a b h)) = iL (Xd κ) / iL (ww (a : K) (b : K)) := by
  rw [sum_H S κ hκ]
  have hp : ∀ Q ∈ κ.S, 1 / iL (MvPowerSeries.map jK (wh a b (hQ S Q))) +
      1 / iL (MvPowerSeries.map jK (wh a b (-hQ S Q))) =
      -(iL (C (Velu.Kernel.tQ Q) * rQ Q ^ 2 + 2 * C (Velu.Kernel.uQ Q) * rQ Q ^ 3)) /
        iL (ww (a : K) (b : K)) := by
    intro Q hQ'
    have hs := hQ_spec S κ hκ hQ'
    have := pair_identity (a := a) (b := b) (hQ_ne S κ hκ hQ') (norm_lt_one_of_tn (S.tn _ hs.1))
    rwa [hs.2] at this
  rw [Finset.sum_congr rfl hp, wh_zero, map_w_short, Xd, map_sub, map_one, map_sum,
    ← Finset.sum_div, Finset.sum_neg_distrib]
  ring

omit hκ in
lemma prod_ite_mul {M : Type*} [CommMonoid M] (f : 𝒪 → M) {h : 𝒪} (hh : h ∈ S.H) :
    (∏ h' ∈ S.H, (if h' = h then 1 else f h')) * f h = ∏ h' ∈ S.H, f h' := by
  classical
  rw [← Finset.mul_prod_erase _ _ hh, ← Finset.mul_prod_erase _ (fun h' => f h') hh, if_pos rfl,
    one_mul, mul_comm]
  congr 1
  exact Finset.prod_congr rfl fun h' hh' => if_neg (Finset.ne_of_mem_erase hh')

omit hκ in
lemma field_aux {F : Type*} [Field F] (ω Ws X : F) (hω : ω ≠ 0) : ω * Ws * (X / ω) = X * Ws := by
  field_simp

/-- **`Dser = Xd · Wst`** in `K⟦z⟧`. -/
theorem map_Dser :
    MvPowerSeries.map jK (Dser S) = Xd κ * MvPowerSeries.map jK (Wst S) := by
  apply iL_inj
  have hB : ∀ h ∈ S.H, iL (MvPowerSeries.map jK (∏ h' ∈ S.H, (if h' = h then 1 else wh a b h'))) =
      iL (MvPowerSeries.map jK (Wall S)) * (1 / iL (MvPowerSeries.map jK (wh a b h))) := by
    intro h hh
    have hW : iL (MvPowerSeries.map jK (wh a b h)) ≠ 0 := by
      by_cases h0 : h = 0
      · subst h0; rw [wh_zero, map_w_short]; exact ι_ww_ne
      · exact map_wh_ne h0 (norm_lt_one_of_tn (S.tn h hh))
    rw [mul_one_div, eq_div_iff hW, ← map_mul, ← map_mul, prod_ite_mul S _ hh]
    rfl
  rw [Dser, map_sum, map_sum, Finset.sum_congr rfl hB, ← Finset.mul_sum, sum_inv_wh S κ hκ,
    Wall_eq_w_mul, map_mul, map_mul, map_w_short, map_mul]
  exact field_aux _ _ _ ι_ww_ne

end VeluDescent
