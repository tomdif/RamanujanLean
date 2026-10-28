/-
# Chord data for `μ_p` and `⟨s⟩`

`TorsData.ofRing`: chord data over a field `L` from points over a ring `R` mapped by an injective
`j : R → L`, given the cleared chord identities `Ix = Iy = 0` (from `chord_mu` / `chord_sub`).

* `muData`: `X_k = x(ζ^k) + 1/12`, `Y_k = θx(ζ^k)/2` over `K⟦q⟧` (`j = ι ∘ eP`).
* `subData`: `X_k = x(s^k) + 1/12`, `Y_k = θx(s^k)/2` over `K⟦s⟧`, `q = s^p` (`j = ι ∘ rescale ζ^j`).
-/
import RamanujanTau.TateAdd.Coef
import RamanujanTau.TateAdd.Group
import RamanujanTau.TateQuot.Main

set_option autoImplicit false

noncomputable section

namespace TateAdd

open PowerSeries TateQuot Finset

/-! ### Transfer -/

section Transfer
variable {R : Type*} [CommRing R] {L : Type*} [Field L] [CharZero L] [DecidableEq L] {p : ℕ}

/-- chord data over `L` from data over `R`. -/
def TorsData.ofRing (j : R →+* L) (hj : Function.Injective j) (A B : R) (A' B' : L)
    (hA : j A = A') (hB : j B = B') (X Y : ℕ → R)
    (hon : ∀ k, 1 ≤ k → k < p → Y k ^ 2 = X k ^ 3 + A * X k + B)
    (hY : ∀ k, 1 ≤ k → k < p → Y k ≠ 0)
    (hsX : ∀ k, 1 ≤ k → k < p → X (p - k) = X k)
    (hsY : ∀ k, 1 ≤ k → k < p → Y (p - k) = -Y k)
    (hd : ∀ a b, 1 ≤ a → a < b → a + b < p → X a ≠ X b)
    (hI : ∀ a b, 1 ≤ a → a < b → a + b < p → ∃ d1 d2 d3 : R, d1 ≠ 0 ∧ d2 ≠ 0 ∧ d3 ≠ 0 ∧
      Ix (36 * d1 ^ 2 * X a) (216 * d1 ^ 3 * Y a) d1 (36 * d2 ^ 2 * X b) (216 * d2 ^ 3 * Y b) d2
        (36 * d3 ^ 2 * X (a + b)) d3 = 0 ∧
      Iy (36 * d1 ^ 2 * X a) (216 * d1 ^ 3 * Y a) d1 (36 * d2 ^ 2 * X b) (216 * d2 ^ 3 * Y b) d2
        (36 * d3 ^ 2 * X (a + b)) (216 * d3 ^ 3 * Y (a + b)) d3 = 0) :
    TorsData A' B' p where
  X k := j (X k)
  Y k := j (Y k)
  on k h1 h2 := by rw [← hA, ← hB]; simpa using congrArg j (hon k h1 h2)
  Yne k h1 h2 := by rw [Ne, map_eq_zero_iff j hj]; exact hY k h1 h2
  symX k h1 h2 := by rw [hsX k h1 h2]
  symY k h1 h2 := by rw [hsY k h1 h2, map_neg]
  dist a b h1 h2 h3 := fun h => hd a b h1 h2 h3 (hj h)
  chord a b h1 h2 h3 := by
    obtain ⟨d1, d2, d3, n1, n2, n3, hx, hy⟩ := hI a b h1 h2 h3
    have hx' := congrArg j hx
    have hy' := congrArg j hy
    rw [Ix_map, map_zero] at hx'
    rw [Iy_map, map_zero] at hy'
    simp only [map_mul, map_pow, map_ofNat] at hx' hy'
    exact chord_field hx' hy' ((map_ne_zero_iff j hj).mpr n1) ((map_ne_zero_iff j hj).mpr n2)
      ((map_ne_zero_iff j hj).mpr n3) (fun h => hd a b h1 h2 h3 (hj h))

end Transfer

variable {K : Type*} [Field K] [CharZero K] {p : ℕ} [hp : Fact p.Prime]

lemma c12 : (36 : PowerSeries K) * C (1 / 12) = 3 := by
  rw [← map_ofNat (C (R := K)) 36, ← map_mul, ← map_ofNat (C (R := K)) 3]; norm_num
lemma c2 : (216 : PowerSeries K) * C (1 / 2) = 108 := by
  rw [← map_ofNat (C (R := K)) 216, ← map_mul, ← map_ofNat (C (R := K)) 108]; norm_num

/-! ### `μ_p` -/

section Mu
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)

lemma cc_tx (m : ℕ) {w : K} (hw : w ≠ 0) (hw1 : w ≠ 1) : constantCoeff (tx m w) = cK m w := by
  rw [tx_eq hw hw1]; simp [txc]

lemma cK0_eq (w : K) : cK 0 w = w / (w - 1) ^ 2 := by simp [cK, cpoly]
lemma cK1_eq (w : K) : cK 1 w = -(w * (1 + w)) / (w - 1) ^ 3 := by simp [cK, cpoly]

include hζ

lemma zeta_ne_neg_one {k : ℕ} (hk : k ∈ Ico 1 p) (hp2 : p ≠ 2) : ζ ^ k ≠ -1 := by
  intro h
  have h2 : ζ ^ (2 * k) = 1 := by rw [pow_mul', h]; norm_num
  have := hζ.dvd_of_pow_eq_one _ h2
  rw [mem_Ico] at hk
  have hodd : ¬ 2 ∣ p := by
    intro h2p; exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.out).mp h2p).symm
  rcases (Nat.Prime.dvd_mul hp.out).mp this with h | h
  · exact hp2 (le_antisymm (Nat.le_of_dvd (by norm_num) h) hp.out.two_le)
  · exact absurd (Nat.le_of_dvd (by omega) h) (by omega)

lemma cc_Ymu {k : ℕ} (hk : k ∈ Ico 1 p) :
    constantCoeff (Ymu ζ k) = 1 / 2 * cK 1 (ζ ^ k) := by
  rw [Ymu, map_mul, constantCoeff_C, cc_tx 1 (zeta_pow_ne_zero hζ k) (pow_ne_one_Ico hζ hk)]

lemma cc_Ymu_ne {k : ℕ} (hk : k ∈ Ico 1 p) (hp2 : p ≠ 2) : constantCoeff (Ymu ζ k) ≠ 0 := by
  rw [cc_Ymu hζ hk, cK1_eq]
  have h0 := zeta_pow_ne_zero hζ k
  have h1 : ζ ^ k - 1 ≠ 0 := sub_ne_zero.mpr (pow_ne_one_Ico hζ hk)
  have h2 : 1 + ζ ^ k ≠ 0 := by
    intro h; exact zeta_ne_neg_one hζ hk hp2 (by linear_combination h)
  simp [h0, h1, h2]

lemma cc_Ymu_sym {k : ℕ} (hk : k ∈ Ico 1 p) :
    constantCoeff (Ymu ζ (p - k)) = -constantCoeff (Ymu ζ k) := by
  have hk' : p - k ∈ Ico 1 p := by rw [mem_Ico] at hk ⊢; omega
  rw [cc_Ymu hζ hk, cc_Ymu hζ hk', zeta_pow_sub hζ (mem_Ico.mp hk).2.le, cK1_eq, cK1_eq]
  have h0 := zeta_pow_ne_zero hζ k
  have h1 : 1 - ζ ^ k ≠ 0 := sub_ne_zero.mpr (Ne.symm (pow_ne_one_Ico hζ hk))
  have h1' : ζ ^ k - 1 ≠ 0 := sub_ne_zero.mpr (pow_ne_one_Ico hζ hk)
  have e : (ζ ^ k)⁻¹ - 1 = (1 - ζ ^ k) / ζ ^ k := by field_simp
  rw [e]
  field_simp
  ring

lemma Ymu_sym (hp2 : p ≠ 2) {k : ℕ} (hk : k ∈ Ico 1 p) : Ymu ζ (p - k) = -Ymu ζ k := by
  have hk' : p - k ∈ Ico 1 p := by rw [mem_Ico] at hk ⊢; omega
  have hsq : Ymu ζ (p - k) ^ 2 = Ymu ζ k ^ 2 := by
    rw [mu_on_curve hζ hk', mu_on_curve hζ hk, Xmu_sym hζ hk]
  have hne : Ymu ζ (p - k) ≠ Ymu ζ k := by
    intro h
    have := cc_Ymu_sym hζ hk
    rw [h] at this
    exact cc_Ymu_ne hζ hk hp2 (by linear_combination this / 2)
  have : (Ymu ζ (p - k) - Ymu ζ k) * (Ymu ζ (p - k) + Ymu ζ k) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · linear_combination h

lemma cc_Xmu {k : ℕ} (hk : k ∈ Ico 1 p) : constantCoeff (Xmu ζ k) = cK 0 (ζ ^ k) + 1 / 12 := by
  rw [Xmu, map_add, constantCoeff_C, cc_tx 0 (zeta_pow_ne_zero hζ k) (pow_ne_one_Ico hζ hk)]

lemma Xmu_dist {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) (hb : a + b < p) : Xmu ζ a ≠ Xmu ζ b := by
  have hai : a ∈ Ico 1 p := mem_Ico.mpr ⟨ha, by omega⟩
  have hbi : b ∈ Ico 1 p := mem_Ico.mpr ⟨by omega, by omega⟩
  intro h
  have := congrArg constantCoeff h
  rw [cc_Xmu hζ hai, cc_Xmu hζ hbi, cK0_eq, cK0_eq, add_left_inj] at this
  have h1 : ζ ^ a - 1 ≠ 0 := sub_ne_zero.mpr (pow_ne_one_Ico hζ hai)
  have h2 : ζ ^ b - 1 ≠ 0 := sub_ne_zero.mpr (pow_ne_one_Ico hζ hbi)
  field_simp at this
  have key : (ζ ^ a - ζ ^ b) * (1 - ζ ^ a * ζ ^ b) = 0 := by linear_combination this
  rcases mul_eq_zero.mp key with h | h
  · exact absurd (hζ.pow_inj (by omega) (by omega) (sub_eq_zero.mp h)) (by omega)
  · rw [← pow_add] at h
    exact pow_ne_one_Ico hζ (mem_Ico.mpr ⟨by omega, hb⟩) (by linear_combination -h)

lemma Xmu_eq (k : ℕ) (δ : K) :
    36 * (tx 0 (ζ ^ k) * C δ ^ 2) + 3 * C δ ^ 2 = 36 * C δ ^ 2 * Xmu ζ k := by
  rw [Xmu]; linear_combination (-(C δ ^ 2)) * (c12 (K := K))
lemma Ymu_eq (k : ℕ) (δ : K) :
    108 * (tx 1 (ζ ^ k) * C δ ^ 3) = 216 * C δ ^ 3 * Ymu ζ k := by
  rw [Ymu]; linear_combination (-(C δ ^ 3 * tx 1 (ζ ^ k))) * (c2 (K := K))

lemma mu_I {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) (hb : a + b < p) :
    ∃ d1 d2 d3 : PowerSeries K, d1 ≠ 0 ∧ d2 ≠ 0 ∧ d3 ≠ 0 ∧
      Ix (36 * d1 ^ 2 * Xmu ζ a) (216 * d1 ^ 3 * Ymu ζ a) d1 (36 * d2 ^ 2 * Xmu ζ b)
        (216 * d2 ^ 3 * Ymu ζ b) d2 (36 * d3 ^ 2 * Xmu ζ (a + b)) d3 = 0 ∧
      Iy (36 * d1 ^ 2 * Xmu ζ a) (216 * d1 ^ 3 * Ymu ζ a) d1 (36 * d2 ^ 2 * Xmu ζ b)
        (216 * d2 ^ 3 * Ymu ζ b) d2 (36 * d3 ^ 2 * Xmu ζ (a + b)) (216 * d3 ^ 3 * Ymu ζ (a + b))
        d3 = 0 := by
  have hai : a ∈ Ico 1 p := mem_Ico.mpr ⟨ha, by omega⟩
  have hbi : b ∈ Ico 1 p := mem_Ico.mpr ⟨by omega, by omega⟩
  have hci : a + b ∈ Ico 1 p := mem_Ico.mpr ⟨by omega, hb⟩
  have h3 : ζ ^ a * ζ ^ b ≠ 1 := by rw [← pow_add]; exact pow_ne_one_Ico hζ hci
  obtain ⟨hx, hy⟩ := chord_mu (zeta_pow_ne_zero hζ a) (zeta_pow_ne_zero hζ b)
    (pow_ne_one_Ico hζ hai) (pow_ne_one_Ico hζ hbi) h3
  rw [← pow_add, Xmu_eq hζ, Xmu_eq hζ, Xmu_eq hζ, Ymu_eq hζ, Ymu_eq hζ] at hx
  rw [← pow_add, Xmu_eq hζ, Xmu_eq hζ, Xmu_eq hζ, Ymu_eq hζ, Ymu_eq hζ, Ymu_eq hζ] at hy
  have hC : ∀ {w : K}, w ≠ 1 → (C (w - 1) : PowerSeries K) ≠ 0 := fun hw => Cw1_ne hw
  exact ⟨_, _, _, hC (pow_ne_one_Ico hζ hai), hC (pow_ne_one_Ico hζ hbi),
    hC (pow_ne_one_Ico hζ hci), hx, hy⟩

end Mu

/-! ### `⟨s⟩` -/

section Sub

lemma tB_coeff_min {e k : ℕ} (he : e ≤ 1) (hk1 : 1 ≤ k) (hkp : k < p) (hp2 : p ≠ 2) :
    (k < p - k ∧ coeff k (tB K p e k) = 1) ∨ (p - k < k ∧ coeff (p - k) (tB K p e k) = (-1) ^ e) := by
  have hodd : p % 2 = 1 := (hp.out.eq_two_or_odd).resolve_left hp2
  rcases Nat.lt_or_gt_of_ne (show k ≠ p - k by omega) with h | h
  · exact Or.inl ⟨h, coeff_tB_k he hk1 h⟩
  · exact Or.inr ⟨h, coeff_tB_pk he hk1 hkp h⟩

lemma YB_ne (hp2 : p ≠ 2) {k : ℕ} (hk1 : 1 ≤ k) (hkp : k < p) : YB K p k ≠ 0 := by
  intro h
  rw [YB] at h
  rcases tB_coeff_min (K := K) (e := 1) le_rfl hk1 hkp hp2 with ⟨-, h1⟩ | ⟨-, h1⟩
  · have := congrArg (coeff k) h
    rw [coeff_C_mul, h1, map_zero] at this; norm_num at this
  · have := congrArg (coeff (p - k)) h
    rw [coeff_C_mul, h1, map_zero] at this; norm_num at this

lemma YB_sym (hp2 : p ≠ 2) {k : ℕ} (hk1 : 1 ≤ k) (hkp : k < p) : YB K p (p - k) = -YB K p k := by
  have hk : k ∈ Ico 1 p := mem_Ico.mpr ⟨hk1, hkp⟩
  have hk' : p - k ∈ Ico 1 p := by rw [mem_Ico] at hk ⊢; omega
  have hsq : YB K p (p - k) ^ 2 = YB K p k ^ 2 := by
    rw [sub_on_curve hk', sub_on_curve hk, XB_sym hk]
  have hne : YB K p (p - k) ≠ YB K p k := by
    intro h
    rw [YB, YB] at h
    have e2 : p - (p - k) = k := by omega
    rcases tB_coeff_min (K := K) (e := 1) le_rfl hk1 hkp hp2 with ⟨hlt, h1⟩ | ⟨hlt, h1⟩
    · rcases tB_coeff_min (K := K) (e := 1) le_rfl (k := p - k) (by omega) (by omega) hp2 with
        ⟨hlt', h2⟩ | ⟨hlt', h2⟩
      · omega
      · rw [e2] at h2
        have := congrArg (coeff k) h
        rw [coeff_C_mul, coeff_C_mul, h1, h2] at this; norm_num at this
    · rcases tB_coeff_min (K := K) (e := 1) le_rfl (k := p - k) (by omega) (by omega) hp2 with
        ⟨hlt', h2⟩ | ⟨hlt', h2⟩
      · have := congrArg (coeff (p - k)) h
        rw [coeff_C_mul, coeff_C_mul, h1, h2] at this; norm_num at this
      · omega
  have : (YB K p (p - k) - YB K p k) * (YB K p (p - k) + YB K p k) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · linear_combination h

lemma coeff_XB {j k : ℕ} (hj : 1 ≤ j) : coeff j (XB K p k) = coeff j (tB K p 0 k) := by
  rw [XB, map_add, coeff_C, if_neg (by omega), add_zero]

lemma XB_dist (hp2 : p ≠ 2) {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) (hb : a + b < p) :
    XB K p a ≠ XB K p b := by
  intro h
  have := congrArg (coeff a) h
  rw [coeff_XB ha, coeff_XB ha, coeff_tB_k (e := 0) (by norm_num) ha (by omega),
    coeff_tB_lt (e := 0) (by norm_num) (by omega) (by omega) hab (by omega)] at this
  exact one_ne_zero this

lemma XB_eq (k : ℕ) :
    36 * (tB K p 0 k * Us K k ^ 2) + 3 * Us K k ^ 2 = 36 * Us K k ^ 2 * XB K p k := by
  rw [XB]; linear_combination (-(Us K k ^ 2)) * (c12 (K := K))
lemma YB_eq (k : ℕ) : 108 * (tB K p 1 k * Us K k ^ 3) = 216 * Us K k ^ 3 * YB K p k := by
  rw [YB]; linear_combination (-(Us K k ^ 3 * tB K p 1 k)) * (c2 (K := K))

lemma sub_I {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) (hb : a + b < p) :
    ∃ d1 d2 d3 : PowerSeries K, d1 ≠ 0 ∧ d2 ≠ 0 ∧ d3 ≠ 0 ∧
      Ix (36 * d1 ^ 2 * XB K p a) (216 * d1 ^ 3 * YB K p a) d1 (36 * d2 ^ 2 * XB K p b)
        (216 * d2 ^ 3 * YB K p b) d2 (36 * d3 ^ 2 * XB K p (a + b)) d3 = 0 ∧
      Iy (36 * d1 ^ 2 * XB K p a) (216 * d1 ^ 3 * YB K p a) d1 (36 * d2 ^ 2 * XB K p b)
        (216 * d2 ^ 3 * YB K p b) d2 (36 * d3 ^ 2 * XB K p (a + b))
        (216 * d3 ^ 3 * YB K p (a + b)) d3 = 0 := by
  obtain ⟨hx, hy⟩ := chord_sub (K := K) (p := p) ha (by omega : 1 ≤ b) hb
  rw [XB_eq, XB_eq, XB_eq, YB_eq, YB_eq] at hx
  rw [XB_eq, XB_eq, XB_eq, YB_eq, YB_eq, YB_eq] at hy
  exact ⟨_, _, _, Us_ne ha, Us_ne (by omega), Us_ne (by omega), hx, hy⟩

end Sub

end TateAdd
