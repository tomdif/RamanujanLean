/-
# Theta spaces: nonvanishing, products, the factor theorem and the zero count

* `θ_ne_zero` — `θ(c tᵉ) ≠ 0` unless `tᵉ = Q^a` and `c = 1`.
* `conv_thS_mem` — multiplying by the theta series of a point raises the degree by one.
* `factor` — an element of `Th (m+1)` (`m ≥ 1`) vanishing at `p` is `j(x/p) · G` with `G ∈ Th m`.
* `zero_count` — an element of `Th m` vanishing at `m + 1` pairwise inequivalent points is zero.
-/
import RamanujanTau.MTC.ThSpace

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset

/-! ## Nonvanishing of theta at monomials -/

section NonVanish
variable {N : ℕ} (hN : 1 ≤ N)
include hN

lemma θ_coeff (e : ℤ) (c : ℂ) (n : ℤ) :
    (θ hN e c).coeff n = ∑ᶠ k, if thE N e k = n then thC c k else 0 := by
  rw [θ, hs, SummableFamily.coeff_hsum]
  refine finsum_congr fun k => ?_
  simp only [thF, monoFam_apply, mono]
  rw [coeff_single]
  split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; omega)

/-- if `k₀` is the unique index with exponent `n`, the `n`-th coefficient is its term. -/
lemma θ_coeff_unique (e : ℤ) (c : ℂ) (k₀ : ℤ) (hu : ∀ k, thE N e k = thE N e k₀ → k = k₀) :
    (θ hN e c).coeff (thE N e k₀) = thC c k₀ := by
  rw [θ_coeff, finsum_eq_single _ k₀]
  · simp
  · intro k hk; rw [if_neg]; exact fun h => hk (hu k h)

lemma θ_ne_zero {e : ℤ} {c : ℂ} (hc : c ≠ 0) (h : ∀ a : ℤ, e = N * a → c ≠ 1) : θ hN e c ≠ 0 := by
  by_cases hd : (N : ℤ) ∣ e
  · obtain ⟨a, rfl⟩ := hd
    have hc1 := h a rfl
    -- exponents `N c2 k + N a k`; the minimum is attained exactly at `k ∈ {−a, 1 − a}`
    intro h0
    have hcoef := congrArg (fun f : L => f.coeff (thE N (N * a) (-a))) h0
    simp only [HahnSeries.coeff_zero] at hcoef
    rw [θ_coeff] at hcoef
    have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
    have hset : ∀ k, thE N (N * a) k = thE N (N * a) (-a) ↔ k = -a ∨ k = 1 - a := by
      intro k
      unfold thE
      have e1 := two_c2 k; have e2 := two_c2 (-a)
      constructor
      · intro hk
        have : (N : ℤ) * ((k + a) * (k + a - 1)) = 0 := by nlinarith
        rcases mul_eq_zero.mp this with h | h
        · omega
        · rcases mul_eq_zero.mp h with h | h <;> [left; right] <;> linarith
      · rintro (rfl | rfl)
        · rfl
        · have e3 := two_c2 (1 - a); nlinarith
    rw [finsum_eq_sum_of_support_subset (s := {-a, 1 - a})] at hcoef
    · rw [Finset.sum_pair (by omega), if_pos ((hset _).mpr (Or.inl rfl)),
        if_pos ((hset _).mpr (Or.inr rfl))] at hcoef
      simp only [thC] at hcoef
      rw [show (1 : ℤ) - a = -a + 1 by ring, zpow_add_one₀ (by norm_num : (-1 : ℂ) ≠ 0),
        zpow_add_one₀ hc] at hcoef
      have hz : ((-1 : ℂ)) ^ (-a) * c ^ (-a) ≠ 0 := mul_ne_zero (zpow_ne_zero _ (by norm_num)) (zpow_ne_zero _ hc)
      apply hc1
      have : ((-1 : ℂ)) ^ (-a) * c ^ (-a) * (1 - c) = 0 := by linear_combination hcoef
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hz
      · linear_combination -h
    · intro k hk
      rw [Function.mem_support] at hk
      by_contra hk'
      apply hk
      rw [if_neg]
      intro hk2
      rcases (hset k).mp hk2 with rfl | rfl <;> simp at hk'
  · -- unique minimizer `k₀` with `N(k₀−1) + e < 0 < N k₀ + e`
    have hN' : (0 : ℤ) < N := by exact_mod_cast hN
    set k₀ := -(e / N) with hk₀
    have hlo : N * (k₀ - 1) + e < 0 := by
      have := Int.emod_add_ediv e N
      have hm : 0 ≤ e % N := Int.emod_nonneg _ hN'.ne'
      have hm' : e % N < N := Int.emod_lt_of_pos _ hN'
      have hne : e % N ≠ 0 := fun h0 => hd (Int.dvd_of_emod_eq_zero h0)
      rw [hk₀]; nlinarith
    have hhi : 0 < N * k₀ + e := by
      have := Int.emod_add_ediv e N
      have hm : 0 ≤ e % N := Int.emod_nonneg _ hN'.ne'
      have hne : e % N ≠ 0 := fun h0 => hd (Int.dvd_of_emod_eq_zero h0)
      rw [hk₀, mul_neg]; omega
    have hu : ∀ k, thE N e k = thE N e k₀ → k = k₀ := by
      intro k hk
      unfold thE at hk
      have e1 := two_c2 k; have e2 := two_c2 k₀
      have key : (k - k₀) * (N * (k + k₀ - 1) + 2 * e) = 0 := by nlinarith
      rcases mul_eq_zero.mp key with h | h
      · linarith
      · by_contra hne
        rcases lt_or_gt_of_ne hne with hk' | hk' <;> nlinarith
    intro h0
    have := θ_coeff_unique hN e c k₀ hu
    rw [h0, HahnSeries.coeff_zero] at this
    exact mul_ne_zero (zpow_ne_zero _ (by norm_num)) (zpow_ne_zero _ hc) this.symm

end NonVanish

/-! ## Linearity of the Cauchy product and products with points -/

section ConvLin

lemma conv_add_right {F G H : ℤ → L} (hF : Ent F) (hG : Ent G) (hH : Ent H) :
    MTC.conv F (G + H) = MTC.conv F G + MTC.conv F H := by
  funext k
  rw [Pi.add_apply, conv_eq hF (hG.add hH), conv_eq hF hG, conv_eq hF hH, hs, hs, hs,
    ← SummableFamily.hsum_add]
  congr 1; ext i : 1; simp [mul_add]

lemma conv_smul_right {F G : ℤ → L} (hF : Ent F) (hG : Ent G) (a : L) :
    MTC.conv F (a • G) = a • MTC.conv F G := by
  have hG' : Ent (a • G) := hG.smul a
  funext k
  rw [Pi.smul_apply, conv_eq hF hG', conv_eq hF hG, smul_eq_mul, hs, hs, ← SummableFamily.hsum_smul]
  congr 1; ext i : 1
  simp [HahnSeries.of_symm_smul_of_eq_mul, mul_left_comm]

end ConvLin

/-! ## Products with the theta series of a point -/

section Prod
variable {NQ : ℕ} (hNQ : 1 ≤ NQ)
include hNQ

lemma setNZ_infinite : ({c : ℂ | c ≠ 0} : Set ℂ).Infinite := by
  have : ({c : ℂ | c ≠ 0} : Set ℂ) = Set.univ \ {0} := by ext; simp
  rw [this]; exact Set.infinite_univ.diff (Set.finite_singleton 0)

lemma conv_thS_mem {m : ℕ} (hm : 1 ≤ m) (ep : ℤ) {cp : ℂ} (hcp : cp ≠ 0) {eμ : ℤ} {cμ : ℂ} (hcμ : cμ ≠ 0)
    {G : ℤ → L} (hG : G ∈ Th NQ m (mono eμ cμ)) :
    MTC.conv (thS (NQ := NQ) ep cp) G ∈ Th NQ (m + 1) (mono (ep + eμ) (-cp * cμ)) := by
  have hT := thS_mem (NQ := NQ) ep hcp
  have hTE : Ent (thS (NQ := NQ) ep cp) := Th.ent le_rfl (neg_ne_zero.mpr hcp) hNQ hT
  have hGE : Ent G := Th.ent hm hcμ hNQ hG
  refine mem_Th_of_ev (hTE.conv hGE) 0 _ (setNZ_infinite hNQ) (fun c hc => hc) fun c hc => ?_
  rw [ev_conv hTE hGE _ hc, ev_conv hTE hGE _ hc, Th.ev_shift le_rfl (neg_ne_zero.mpr hcp) hNQ hT 0 hc,
    Th.ev_shift hm hcμ hNQ hG 0 hc]
  have : mono (ep + eμ) (-cp * cμ) = mono ep (-cp) * mono eμ cμ := by rw [mono_mul]
  rw [this]
  simp only [zero_mul, neg_zero, Nat.cast_one, Nat.cast_add]
  rw [show (-((m : ℤ) + 1)) = -1 + -(m : ℤ) by ring, zpow_add₀ (show c ≠ 0 from hc)]
  have h1 : mono 0 (c ^ (-1 : ℤ) * c ^ (-(m : ℤ))) = mono 0 (c ^ (-1 : ℤ)) * mono 0 (c ^ (-(m : ℤ))) := by
    rw [mono_mul, add_zero]
  rw [h1]; ring

end Prod

/-! ## Coordinates -/

section Coord
variable {NQ : ℕ}

/-- the element of `Th m μ` with prescribed values `a 0, …, a (m−1)`. -/
noncomputable def extF (m : ℕ) (eμ : ℤ) (cμ : ℂ) (a : Fin m → L) : ℤ → L := fun k => by
  classical
  exact if h : 0 < m then
    mono (-(eμ * (k / m)) + NQ * ((k % m) * (k / m) + m * c2 (k / m))) (cμ ^ (-(k / m))) *
      a ⟨(k % m).toNat, by
        have := Int.emod_lt_of_pos k (show (0 : ℤ) < m by exact_mod_cast h)
        have := Int.emod_nonneg k (show (m : ℤ) ≠ 0 by exact_mod_cast h.ne')
        omega⟩
  else 0

lemma extF_mem {m : ℕ} (hm : 1 ≤ m) (eμ : ℤ) {cμ : ℂ} (hcμ : cμ ≠ 0) (a : Fin m → L) :
    extF (NQ := NQ) m eμ cμ a ∈ Th NQ m (mono eμ cμ) := by
  intro k
  have hm0 : (0 : ℤ) < m := by exact_mod_cast hm
  simp only [extF, dif_pos (show 0 < m by omega)]
  have h1 : (k + m) % m = k % m := by simp
  have h2 : (k + m) / m = k / m + 1 := by rw [Int.add_ediv_of_dvd_right (dvd_refl _), Int.ediv_self hm0.ne']
  simp only [h1, h2]
  rw [← mul_assoc, ← mul_assoc, mono_mul, mono_mul]
  congr 2
  · rw [c2_succ]
    have := Int.emod_add_ediv k m
    nlinarith
  · rw [show -(k / (m : ℤ) + 1) = -1 + -(k / m) by ring, zpow_add₀ hcμ, zpow_neg_one, ← mul_assoc,
      mul_inv_cancel₀ hcμ, one_mul]

lemma extF_val {m : ℕ} (hm : 1 ≤ m) (eμ : ℤ) (cμ : ℂ) (a : Fin m → L) (i : Fin m) :
    extF (NQ := NQ) m eμ cμ a i = a i := by
  simp only [extF, dif_pos (show 0 < m by omega)]
  have h1 : ((i : ℕ) : ℤ) % m = i := Int.emod_eq_of_lt (by omega) (by exact_mod_cast i.2)
  have h2 : ((i : ℕ) : ℤ) / m = 0 := Int.ediv_eq_zero_of_lt (by omega) (by exact_mod_cast i.2)
  simp only [h1, h2]
  simp [c2, mono]

/-- elements of `Th m μ` are determined by their first `m` coefficients. -/
lemma Th.eq_zero_of_coord {m : ℕ} (hm : 1 ≤ m) {eμ : ℤ} {cμ : ℂ} (hcμ : cμ ≠ 0) {F : ℤ → L}
    (hF : F ∈ Th NQ m (mono eμ cμ)) (h0 : ∀ i : Fin m, F i = 0) : F = 0 := by
  funext k
  have hm0 : (0 : ℤ) < m := by exact_mod_cast hm
  have hk : k = k % m + m * (k / m) := (Int.emod_add_ediv k m).symm
  rw [hk, Th.closed hcμ hF]
  have hi : F (k % m) = 0 := by
    have := h0 ⟨(k % m).toNat, by
      have := Int.emod_lt_of_pos k hm0; have := Int.emod_nonneg k hm0.ne'; omega⟩
    simpa [Int.toNat_of_nonneg (Int.emod_nonneg k hm0.ne')] using this
  rw [hi, mul_zero, Pi.zero_apply]

/-- the coordinate map. -/
noncomputable def coordL (m : ℕ) (μ : L) : Th NQ m μ →ₗ[L] (Fin m → L) where
  toFun F i := F.1 i
  map_add' F G := by ext i; simp
  map_smul' a F := by ext i; simp

lemma finrank_Th {m : ℕ} (hm : 1 ≤ m) (eμ : ℤ) {cμ : ℂ} (hcμ : cμ ≠ 0) :
    Module.finrank L (Th NQ m (mono eμ cμ)) = m := by
  have hbij : Function.Bijective (coordL (NQ := NQ) m (mono eμ cμ)) := by
    constructor
    · intro F G hFG
      have hd : (F : ℤ → L) - G = 0 := Th.eq_zero_of_coord hm hcμ (Submodule.sub_mem _ F.2 G.2) fun i => by
        have := congrFun hFG i; simp only [coordL, LinearMap.coe_mk, AddHom.coe_mk] at this
        simp [this]
      exact Subtype.ext (sub_eq_zero.mp hd)
    · intro a
      refine ⟨⟨extF m eμ cμ a, extF_mem hm eμ hcμ a⟩, ?_⟩
      funext i; exact extF_val hm eμ cμ a i
  rw [LinearEquiv.finrank_eq (LinearEquiv.ofBijective _ hbij), Module.finrank_fin_fun]

end Coord

/-! ## Two basis elements and their values -/

section Basis
variable {NQ : ℕ} (hNQ : 1 ≤ NQ)
include hNQ

lemma negpow_aux {cμ : ℂ} (hcμ : cμ ≠ 0) (j : ℤ) : ((-1 : ℂ)) ^ j * (-cμ) ^ (-j) = cμ ^ (-j) := by
  rw [neg_eq_neg_one_mul cμ, mul_zpow, ← mul_assoc, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), add_neg_cancel,
    zpow_zero, one_mul]

/-- value of the first basis vector: a theta function in `x^m`. -/
lemma ev_b0 {m : ℕ} (hm : 1 ≤ m) (eμ : ℤ) {cμ : ℂ} (hcμ : cμ ≠ 0) (e : ℤ) {c : ℂ} (hc : c ≠ 0) :
    ev (extF (NQ := NQ) m eμ cμ (Pi.single ⟨0, by omega⟩ 1)) e c =
      θ (N := NQ * m) (by nlinarith) (m * e - eμ) (c ^ (m : ℤ) / (-cμ)) := by
  have hm0 : (0 : ℤ) < m := by omega
  have hNm : 1 ≤ NQ * m := by nlinarith
  have hT : Ent (thS (NQ := NQ * m) eμ (-cμ)) :=
    Th.ent le_rfl (by simpa using hcμ) hNm (thS_mem (NQ := NQ * m) eμ (neg_ne_zero.mpr hcμ))
  have heq : extF (NQ := NQ) m eμ cμ (Pi.single ⟨0, by omega⟩ 1) =
      subst (thS (NQ := NQ * m) eμ (-cμ)) m 0 1 := by
    funext k
    simp only [extF, dif_pos (show 0 < m by omega), subst, Pi.single_apply, Fin.ext_iff]
    by_cases hk : (m : ℤ) ∣ k
    · obtain ⟨j, rfl⟩ := hk
      have h1 : (m : ℤ) * j % m = 0 := Int.mul_emod_right _ _
      have h2 : (m : ℤ) * j / m = j := Int.mul_ediv_cancel_left _ hm0.ne'
      simp only [h1, h2, if_pos (dvd_mul_right (m : ℤ) j), Int.toNat_zero, if_true, mul_one, thS,
        zero_mul, one_zpow, mono_mul, add_zero]
      congr 1
      · push_cast; ring
      · rw [negpow_aux hNQ hcμ]
    · rw [if_neg hk]
      have hr : k % m ≠ 0 := fun h => hk (Int.dvd_of_emod_eq_zero h)
      have h0 := Int.emod_nonneg k hm0.ne'
      rw [if_neg (by omega), mul_zero]
  rw [heq, ev_subst hT (by omega : (m : ℤ) ≠ 0), thS_ev hNm eμ (neg_ne_zero.mpr hcμ), zero_add, one_mul]

/-- value of the second basis vector: `x` times a theta function in `x^m`. -/
lemma ev_b1 {m : ℕ} (hm : 2 ≤ m) (eμ : ℤ) {cμ : ℂ} (hcμ : cμ ≠ 0) (e : ℤ) {c : ℂ} (hc : c ≠ 0) :
    ev (extF (NQ := NQ) m eμ cμ (Pi.single ⟨1, by omega⟩ 1)) e c =
      mono e c * θ (N := NQ * m) (by nlinarith) (m * e - eμ + NQ) (c ^ (m : ℤ) / (-cμ)) := by
  have hm0 : (0 : ℤ) < m := by omega
  have hNm : 1 ≤ NQ * m := by nlinarith
  have hT : Ent (thS (NQ := NQ * m) (eμ - NQ) (-cμ)) :=
    Th.ent le_rfl (by simpa using hcμ) hNm (thS_mem (NQ := NQ * m) (eμ - NQ) (neg_ne_zero.mpr hcμ))
  have heq : extF (NQ := NQ) m eμ cμ (Pi.single ⟨1, by omega⟩ 1) =
      shiftS (subst (thS (NQ := NQ * m) (eμ - NQ) (-cμ)) m 0 1) (-1) := by
    funext k
    simp only [extF, dif_pos (show 0 < m by omega), shiftS, subst, Pi.single_apply, Fin.ext_iff]
    by_cases hk : (m : ℤ) ∣ (k + -1)
    · obtain ⟨j, hj⟩ := hk
      have hk' : k = 1 + m * j := by linarith
      have h1 : k % m = 1 := by
        rw [hk', Int.add_mul_emod_self_left]; exact Int.emod_eq_of_lt (by norm_num) (by omega)
      have h2 : k / m = j := by
        rw [hk', Int.add_mul_ediv_left _ _ hm0.ne', Int.ediv_eq_zero_of_lt (by norm_num) (by omega), zero_add]
      have h3 : (k + -1) / m = j := by rw [hj, Int.mul_ediv_cancel_left _ hm0.ne']
      simp only [h1, h2, h3, if_pos (show (m : ℤ) ∣ (k + -1) from ⟨j, hj⟩), if_true, mul_one, thS,
        zero_mul, one_zpow, mono_mul, add_zero]
      rw [if_pos (by simp), negpow_aux hNQ hcμ]
      push_cast; ring_nf
    · rw [if_neg hk]
      have h0 := Int.emod_nonneg k hm0.ne'
      rw [if_neg, mul_zero]
      intro h
      apply hk
      have h1 : k % m = 1 := by omega
      exact ⟨k / m, by have := Int.emod_add_ediv k m; linarith⟩
  rw [heq, MTC.ev_shift (hT.subst (by omega) 0 1) (-1) e hc, ev_subst hT (by omega : (m : ℤ) ≠ 0),
    thS_ev hNm _ (neg_ne_zero.mpr hcμ), zero_add, one_mul]
  simp only [mul_neg, mul_one, neg_neg, zpow_neg, inv_inv, zpow_one]
  congr 2; ring

/-- evaluation at a point is a nonzero functional on `Th m μ` for `m ≥ 2`. -/
lemma exists_ev_ne {m : ℕ} (hm : 2 ≤ m) (eμ : ℤ) {cμ : ℂ} (hcμ : cμ ≠ 0) (ep : ℤ) {cp : ℂ} (hcp : cp ≠ 0) :
    ∃ F ∈ Th NQ m (mono eμ cμ), ev F ep cp ≠ 0 := by
  have hNm : 1 ≤ NQ * m := by nlinarith
  by_contra hall
  push Not at hall
  have h0 := hall _ (extF_mem (by omega) eμ hcμ (Pi.single ⟨0, by omega⟩ 1))
  have h1 := hall _ (extF_mem (by omega) eμ hcμ (Pi.single ⟨1, by omega⟩ 1))
  rw [ev_b0 hNQ (by omega) eμ hcμ ep hcp] at h0
  rw [ev_b1 hNQ hm eμ hcμ ep hcp] at h1
  have hz : cp ^ (m : ℤ) / (-cμ) ≠ 0 := div_ne_zero (zpow_ne_zero _ hcp) (neg_ne_zero.mpr hcμ)
  have hmono : mono ep cp ≠ 0 := by rw [mono, Ne, single_eq_zero_iff]; exact hcp
  have h1' := (mul_eq_zero.mp h1).resolve_left hmono
  obtain ⟨a, ha⟩ : ∃ a : ℤ, (m * ep - eμ) = ((NQ * m : ℕ) : ℤ) * a := by
    by_contra hn
    exact θ_ne_zero hNm hz (fun a ha => absurd ⟨a, ha⟩ hn) h0
  obtain ⟨b, hb⟩ : ∃ b : ℤ, (m * ep - eμ + NQ) = ((NQ * m : ℕ) : ℤ) * b := by
    by_contra hn
    exact θ_ne_zero hNm hz (fun a ha => absurd ⟨a, ha⟩ hn) h1'
  push_cast at ha hb
  have hNQ' : (0 : ℤ) < NQ := by exact_mod_cast hNQ
  have key : (NQ : ℤ) * 1 = NQ * (m * (b - a)) := by linarith
  have h1m : (1 : ℤ) = m * (b - a) := mul_left_cancel₀ hNQ'.ne' key
  have hm' : (2 : ℤ) ≤ m := by exact_mod_cast hm
  rcases lt_trichotomy (b - a) 0 with h | h | h <;> nlinarith

end Basis

/-! ## The factor theorem and the zero count -/

section Factor
variable {NQ : ℕ} (hNQ : 1 ≤ NQ)
include hNQ

lemma θ_zero_imp {e : ℤ} {c : ℂ} (hc : c ≠ 0) (h : θ hNQ e c = 0) : ∃ a : ℤ, e = NQ * a ∧ c = 1 := by
  by_contra hn
  push Not at hn
  exact θ_ne_zero hNQ hc hn h

omit hNQ in
lemma conv_zero_right {F : ℤ → L} (hF : Ent F) : MTC.conv F (fun _ => 0) = fun _ => 0 := by
  funext k
  rw [conv_eq hF ent_zero, hs]
  ext n; simp [SummableFamily.coeff_hsum]

omit hNQ in
lemma mono_fix (eμ ep : ℤ) {cμ cp : ℂ} (hcp : cp ≠ 0) :
    mono (ep + (eμ - ep)) (-cp * (cμ / -cp)) = mono eμ cμ := by
  congr 1
  · ring
  · field_simp

omit hNQ in
lemma extF_add (m : ℕ) (eμ : ℤ) (cμ : ℂ) (a b : Fin m → L) :
    extF (NQ := NQ) m eμ cμ (a + b) = extF (NQ := NQ) m eμ cμ a + extF (NQ := NQ) m eμ cμ b := by
  funext k; simp only [extF, Pi.add_apply]; split_ifs <;> ring

omit hNQ in
lemma extF_smul (m : ℕ) (eμ : ℤ) (cμ : ℂ) (c : L) (a : Fin m → L) :
    extF (NQ := NQ) m eμ cμ (c • a) = c • extF (NQ := NQ) m eμ cμ a := by
  funext k; simp only [extF, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring

omit hNQ in
/-- an element of a theta space is the extension of its coordinates. -/
lemma extF_coord {m : ℕ} (hm : 1 ≤ m) {eμ : ℤ} {cμ : ℂ} (hcμ : cμ ≠ 0) {F : ℤ → L}
    (hF : F ∈ Th NQ m (mono eμ cμ)) : extF (NQ := NQ) m eμ cμ (fun i => F i) = F := by
  have hd := Submodule.sub_mem _ (extF_mem hm eμ hcμ (fun i : Fin m => F i)) hF
  exact sub_eq_zero.mp (Th.eq_zero_of_coord hm hcμ hd fun i => by
    simp [extF_val (NQ := NQ) hm eμ cμ])

/-- **factor theorem**: an element of `Th (m+1)` (`m ≥ 1`) vanishing at `p` is `j(x/p)·G`, `G ∈ Th m`. -/
theorem factor {m : ℕ} (hm : 1 ≤ m) {eμ : ℤ} {cμ : ℂ} (hcμ : cμ ≠ 0) (ep : ℤ) {cp : ℂ} (hcp : cp ≠ 0)
    {F : ℤ → L} (hF : F ∈ Th NQ (m + 1) (mono eμ cμ)) (h0 : ev F ep cp = 0) :
    ∃ G ∈ Th NQ m (mono (eμ - ep) (cμ / -cp)), F = MTC.conv (thS (NQ := NQ) ep cp) G := by
  have hc' : cμ / -cp ≠ 0 := div_ne_zero hcμ (neg_ne_zero.mpr hcp)
  have hT : Ent (thS (NQ := NQ) ep cp) := Th.ent le_rfl (neg_ne_zero.mpr hcp) hNQ (thS_mem ep hcp)
  have hm1 : 1 ≤ m + 1 := by omega
  set ext1 : (Fin m → L) → (ℤ → L) := extF (NQ := NQ) m (eμ - ep) (cμ / -cp)
  set ext2 : (Fin (m + 1) → L) → (ℤ → L) := extF (NQ := NQ) (m + 1) eμ cμ
  have hmem1 : ∀ a, ext1 a ∈ Th NQ m (mono (eμ - ep) (cμ / -cp)) := fun a => extF_mem hm _ hc' a
  have hmem2 : ∀ v, ext2 v ∈ Th NQ (m + 1) (mono eμ cμ) := fun v => extF_mem hm1 _ hcμ v
  have hE1 : ∀ a, Ent (ext1 a) := fun a => Th.ent hm hc' hNQ (hmem1 a)
  have hE2 : ∀ v, Ent (ext2 v) := fun v => Th.ent hm1 hcμ hNQ (hmem2 v)
  have hprod : ∀ a, MTC.conv (thS (NQ := NQ) ep cp) (ext1 a) ∈ Th NQ (m + 1) (mono eμ cμ) := fun a => by
    have := conv_thS_mem hNQ hm ep hcp hc' (hmem1 a); rwa [mono_fix eμ ep hcp] at this
  -- the linear maps on coordinates
  let A : (Fin m → L) →ₗ[L] (Fin (m + 1) → L) :=
    { toFun := fun a i => MTC.conv (thS (NQ := NQ) ep cp) (ext1 a) i
      map_add' := fun a b => by
        funext i
        simp only [ext1, extF_add, Pi.add_apply]
        rw [conv_add_right hT (hE1 a) (hE1 b)]; rfl
      map_smul' := fun c a => by
        funext i
        simp only [ext1, extF_smul, Pi.smul_apply, RingHom.id_apply]
        rw [conv_smul_right hT (hE1 a) c]; rfl }
  let φ : (Fin (m + 1) → L) →ₗ[L] L :=
    { toFun := fun v => ev (ext2 v) ep cp
      map_add' := fun v w => by simp only [ext2, extF_add]; exact ev_add (hE2 v) (hE2 w) ep cp
      map_smul' := fun c v => by
        simp only [ext2, extF_smul, RingHom.id_apply]; exact ev_smul (hE2 v) c ep cp }
  have hA_ext : ∀ a, ext2 (A a) = MTC.conv (thS (NQ := NQ) ep cp) (ext1 a) := fun a =>
    extF_coord hm1 hcμ (hprod a)
  -- injectivity of `A`
  have hinj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    have hz : MTC.conv (thS (NQ := NQ) ep cp) (ext1 a) = 0 := by
      rw [← hA_ext, ha]; funext k; simp [ext2, extF]
    have hS : ({c : ℂ | c ≠ 0 ∧ c ≠ cp} : Set ℂ).Infinite := by
      have : ({c : ℂ | c ≠ 0 ∧ c ≠ cp} : Set ℂ) = (Set.univ \ {0}) \ {cp} := by ext; simp [and_comm]
      rw [this]; exact (Set.infinite_univ.diff (Set.finite_singleton 0)).diff (Set.finite_singleton cp)
    have h1 := eq_zero_of_ev (hE1 a) ep _ hS fun c hc => by
      have e1 := ev_conv hT (hE1 a) ep hc.1
      rw [hz, show (0 : ℤ → L) = fun _ => 0 from rfl, ev_zero, thS_ev hNQ ep hcp, sub_self] at e1
      have hθ : θ hNQ 0 (c / cp) ≠ 0 := θ_ne_zero hNQ (div_ne_zero hc.1 hcp) fun a _ h1 =>
        hc.2 (by field_simp at h1; exact h1)
      exact (mul_eq_zero.mp e1.symm).resolve_left hθ
    funext i
    have := congrFun h1 i
    have h2 : ext1 a (i : ℕ) = a i := extF_val (NQ := NQ) hm _ _ a i
    rw [h2] at this; exact this
  -- `φ ∘ A = 0`
  have hle : LinearMap.range A ≤ LinearMap.ker φ := by
    rintro _ ⟨a, rfl⟩
    rw [LinearMap.mem_ker]
    change ev (ext2 (A a)) ep cp = 0
    rw [hA_ext, ev_conv hT (hE1 a) ep hcp, thS_ev hNQ ep hcp, sub_self, div_self hcp, θ_one, zero_mul]
  -- dimensions
  have hφ0 : φ ≠ 0 := by
    obtain ⟨G, hG, hne⟩ := exists_ev_ne hNQ (show 2 ≤ m + 1 by omega) eμ hcμ ep hcp
    intro h
    apply hne
    have := LinearMap.congr_fun h (fun i => G i)
    change ev (ext2 fun i => G i) ep cp = 0 at this
    rwa [show ext2 (fun i => G i) = G from extF_coord hm1 hcμ hG] at this
  have hrφ : Module.finrank L (LinearMap.range φ) = 1 := by
    have h1 : Module.finrank L (LinearMap.range φ) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range φ); rwa [Module.finrank_self] at this
    have h2 : Module.finrank L (LinearMap.range φ) ≠ 0 := by
      rw [Ne, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]; exact hφ0
    omega
  have hkφ : Module.finrank L (LinearMap.ker φ) = m := by
    have := LinearMap.finrank_range_add_finrank_ker φ
    rw [hrφ, Module.finrank_fin_fun] at this; omega
  have hrA : Module.finrank L (LinearMap.range A) = m := by
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]
  have heq := Submodule.eq_of_le_of_finrank_eq hle (hrA.trans hkφ.symm)
  have hv : (fun i : Fin (m + 1) => F i) ∈ LinearMap.ker φ := by
    rw [LinearMap.mem_ker]
    change ev (ext2 fun i => F i) ep cp = 0
    rwa [show ext2 (fun i => F i) = F from extF_coord hm1 hcμ hF]
  rw [← heq] at hv
  obtain ⟨a, ha⟩ := hv
  refine ⟨ext1 a, hmem1 a, ?_⟩
  rw [← hA_ext a, ha]
  exact (extF_coord hm1 hcμ hF).symm

/-- `Th 0 μ` elements vanishing at one point are zero. -/
lemma zero_count_zero {eμ : ℤ} {cμ : ℂ} {F : ℤ → L} (hF : F ∈ Th NQ 0 (mono eμ cμ)) (e : ℤ) {c : ℂ}
    (hc : c ≠ 0) (h0 : ev F e c = 0) : F = 0 := by
  by_contra hne
  obtain ⟨k₁, hk₁⟩ : ∃ k, F k ≠ 0 := by
    by_contra h; push Not at h; exact hne (funext h)
  have hμ : mono eμ cμ = mono (NQ * k₁) 1 := by
    have := hF k₁; simp only [Nat.cast_zero, add_zero] at this
    exact mul_right_cancel₀ hk₁ this
  have hsupp : ∀ k, k ≠ k₁ → F k = 0 := by
    intro k hk
    have h := hF k
    simp only [Nat.cast_zero, add_zero, hμ] at h
    have hd : mono (NQ * k₁) (1 : ℂ) - mono (NQ * k) 1 ≠ 0 := by
      intro h'
      have := congrArg (fun f : L => f.coeff (NQ * k₁)) h'
      simp only [mono, coeff_sub, coeff_single_same, HahnSeries.coeff_zero] at this
      rw [coeff_single_of_ne (by
        intro h2; apply hk
        have hN : (NQ : ℤ) ≠ 0 := by exact_mod_cast (show NQ ≠ 0 by omega)
        exact (mul_left_cancel₀ hN h2).symm)] at this
      simp at this
    have : (mono (NQ * k₁) (1 : ℂ) - mono (NQ * k) 1) * F k = 0 := by rw [sub_mul, h, sub_self]
    exact (mul_eq_zero.mp this).resolve_left hd
  have hFm : F = monoS k₁ (F k₁) := by
    funext k; unfold monoS; split_ifs with h
    · rw [h]
    · exact hsupp k h
  rw [hFm, ev_monoS] at h0
  have hm : mono (e * k₁) (c ^ k₁) ≠ 0 := by
    rw [mono, Ne, single_eq_zero_iff]; exact zpow_ne_zero _ hc
  exact hk₁ ((mul_eq_zero.mp h0).resolve_right hm)

/-- **zero count**: an element of `Th m μ` vanishing at `m + 1` pairwise inequivalent points is zero. -/
theorem zero_count : ∀ (m : ℕ) {eμ : ℤ} {cμ : ℂ} (_ : cμ ≠ 0) {F : ℤ → L} (_ : F ∈ Th NQ m (mono eμ cμ))
    (pe : Fin (m + 1) → ℤ) (pc : Fin (m + 1) → ℂ) (_ : ∀ i, pc i ≠ 0)
    (_ : ∀ i j, i ≠ j → ∀ a : ℤ, pe i - pe j = NQ * a → pc i ≠ pc j)
    (_ : ∀ i, ev F (pe i) (pc i) = 0), F = 0 := by
  intro m
  induction m with
  | zero =>
      intro eμ cμ _ F hF pe pc hpc _ hz
      exact zero_count_zero hNQ hF (pe 0) (hpc 0) (hz 0)
  | succ m ih =>
      intro eμ cμ hcμ F hF pe pc hpc hdist hz
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · -- `Th 1`: one coordinate, two inequivalent zeros
        have hb := extF_mem (NQ := NQ) le_rfl eμ hcμ (Pi.single ⟨0, by omega⟩ 1)
        have hv : extF (NQ := NQ) 1 eμ cμ (Pi.single 0 1) 0 = 1 := by
          have := extF_val (NQ := NQ) le_rfl eμ cμ (Pi.single ⟨0, by omega⟩ (1 : L)) ⟨0, by omega⟩
          simpa using this
        have hFb : F = F 0 • extF (NQ := NQ) 1 eμ cμ (Pi.single ⟨0, by omega⟩ 1) := by
          have hd := Submodule.sub_mem _ hF (Submodule.smul_mem _ (F 0) hb)
          have := Th.eq_zero_of_coord le_rfl hcμ hd fun i => by
            fin_cases i
            simp [hv]
          exact sub_eq_zero.mp this
        by_cases hF0 : F 0 = 0
        · rw [hFb, hF0]; funext k; simp
        · exfalso
          have hbE : Ent (extF (NQ := NQ) 1 eμ cμ (Pi.single ⟨0, by omega⟩ 1)) := Th.ent le_rfl hcμ hNQ hb
          have hval : ∀ i, θ (N := NQ * 1) (by omega) (1 * pe i - eμ) (pc i ^ ((1 : ℕ) : ℤ) / -cμ) = 0 := by
            intro i
            have := hz i
            rw [hFb, show F 0 • extF (NQ := NQ) 1 eμ cμ (Pi.single ⟨0, by omega⟩ 1) =
              fun k => F 0 * extF (NQ := NQ) 1 eμ cμ (Pi.single ⟨0, by omega⟩ 1) k from rfl,
              ev_smul hbE, ev_b0 hNQ le_rfl eμ hcμ (pe i) (hpc i)] at this
            exact (mul_eq_zero.mp this).resolve_left hF0
          have hN1 : 1 ≤ NQ * 1 := by omega
          obtain ⟨a, ha, hca⟩ := θ_zero_imp hN1 (div_ne_zero (zpow_ne_zero _ (hpc 0)) (neg_ne_zero.mpr hcμ))
            (hval 0)
          obtain ⟨b, hb', hcb⟩ := θ_zero_imp hN1 (div_ne_zero (zpow_ne_zero _ (hpc 1)) (neg_ne_zero.mpr hcμ))
            (hval 1)
          refine hdist 0 1 (by decide) (a - b) (by push_cast at ha hb'; linarith) ?_
          have h0' : pc 0 = -cμ := by rw [div_eq_one_iff_eq (neg_ne_zero.mpr hcμ)] at hca; simpa using hca
          have h1' : pc 1 = -cμ := by rw [div_eq_one_iff_eq (neg_ne_zero.mpr hcμ)] at hcb; simpa using hcb
          rw [h0', h1']
      · -- factor at the first point and recurse
        obtain ⟨G, hG, rfl⟩ := factor hNQ hm hcμ (pe 0) (hpc 0) hF (hz 0)
        have hc' : cμ / -pc 0 ≠ 0 := div_ne_zero hcμ (neg_ne_zero.mpr (hpc 0))
        have hT : Ent (thS (NQ := NQ) (pe 0) (pc 0)) :=
          Th.ent le_rfl (neg_ne_zero.mpr (hpc 0)) hNQ (thS_mem _ (hpc 0))
        have hGE := Th.ent hm hc' hNQ hG
        have hG0 : G = 0 := ih hc' hG (fun i => pe i.succ) (fun i => pc i.succ) (fun i => hpc _)
          (fun i j hij a ha => hdist _ _ (fun h => hij (Fin.succ_injective _ h)) a ha) fun i => by
            have := hz i.succ
            rw [ev_conv hT hGE _ (hpc _), thS_ev hNQ _ (hpc 0)] at this
            have hθ : θ hNQ (pe i.succ - pe 0) (pc i.succ / pc 0) ≠ 0 :=
              θ_ne_zero hNQ (div_ne_zero (hpc _) (hpc 0)) fun a ha h1 =>
                hdist i.succ 0 (Fin.succ_ne_zero i) a ha ((div_eq_one_iff_eq (hpc 0)).mp h1)
            exact (mul_eq_zero.mp this).resolve_left hθ
        rw [hG0]
        exact conv_zero_right hT

end Factor

end MTC
