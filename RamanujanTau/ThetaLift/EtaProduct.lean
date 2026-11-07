import RamanujanTau.ThetaLift.EtaMultiplier

/-!
# The character of the eta product `η(tz)^j η(z)` on Γ₀(t)

For `t` prime to six and `t + j ≡ 0 (mod 24)`, with `j + 1 = 2w`,

  `Z(γz) = (d/t) (cz+d)^w Z(z)`,   `Z(z) = η(tz)^j η(z)`,

for every `γ = [a b; c d]` with `t ∣ c`. Petersson's formula gives the case of positive odd `c`, and
the rest follows from `-γ` and `γ [1 0; t 1]`.
-/

set_option autoImplicit false

namespace RamanujanTau.ThetaLift
open Complex ModularForm MatrixGroups Rademacher
open scoped Real
open UpperHalfPlane hiding I

noncomputable section

/-- The conjugate `[a tb; c/t d]`. -/
def conjT (t : ℕ) (γ : SL(2, ℤ)) (h : (t : ℤ) ∣ γ 1 0) : SL(2, ℤ) :=
  ⟨!![γ 0 0, t * γ 0 1; γ 1 0 / t, γ 1 1], by
    have hd := γ.property
    rw [Matrix.det_fin_two] at hd
    rw [Matrix.det_fin_two_of]
    have he : (t : ℤ) * (γ 1 0 / t) = γ 1 0 := Int.mul_ediv_cancel' h
    linear_combination hd - γ 0 1 * he⟩

variable {t : ℕ}

lemma coe_conj_00 (γ : SL(2, ℤ)) (h : (t : ℤ) ∣ γ 1 0) : conjT t γ h 0 0 = γ 0 0 := rfl
lemma coe_conj_01 (γ : SL(2, ℤ)) (h : (t : ℤ) ∣ γ 1 0) : conjT t γ h 0 1 = t * γ 0 1 := rfl
lemma coe_conj_10 (γ : SL(2, ℤ)) (h : (t : ℤ) ∣ γ 1 0) : conjT t γ h 1 0 = γ 1 0 / t := rfl
lemma coe_conj_11 (γ : SL(2, ℤ)) (h : (t : ℤ) ∣ γ 1 0) : conjT t γ h 1 1 = γ 1 1 := rfl

lemma lin_conj (ht : t ≠ 0) (γ : SL(2, ℤ)) (h : (t : ℤ) ∣ γ 1 0) (z : ℂ) :
    lin (conjT t γ h) (t * z) = lin γ z := by
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have he : ((γ 1 0 / (t : ℤ) : ℤ) : ℂ) * t = γ 1 0 := by
    exact_mod_cast Int.ediv_mul_cancel h
  unfold lin
  rw [coe_conj_10, coe_conj_11, ← he]
  ring

lemma mob_conj (ht : t ≠ 0) (γ : SL(2, ℤ)) (h : (t : ℤ) ∣ γ 1 0) (z : ℂ) :
    mob (conjT t γ h) (t * z) = t * mob γ z := by
  have hl := lin_conj ht γ h z
  unfold mob
  change ((conjT t γ h 0 0 : ℂ) * (t * z) + conjT t γ h 0 1) / lin (conjT t γ h) (t * z) = _
  rw [hl, coe_conj_00, coe_conj_01]
  change _ = t * (((γ 0 0 : ℂ) * z + γ 0 1) / lin γ z)
  push_cast
  rw [mul_div_assoc']
  congr 1
  ring

lemma e24_pow (n : ℤ) (m : ℕ) : e24 n ^ m = e24 ((m : ℤ) * n) := by
  unfold e24
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma int_sq_sub_one (h2 : ¬ 2 ∣ t) (h3 : ¬ 3 ∣ t) : (24 : ℤ) ∣ (t : ℤ) ^ 2 - 1 := by
  have hs : t % 24 = 1 ∨ t % 24 = 5 ∨ t % 24 = 7 ∨ t % 24 = 11 ∨ t % 24 = 13 ∨ t % 24 = 17 ∨
      t % 24 = 19 ∨ t % 24 = 23 := by omega
  have hm : t ^ 2 % 24 = 1 := by
    rw [Nat.pow_mod]
    rcases hs with h | h | h | h | h | h | h | h <;> rw [h]
  obtain ⟨q, hq⟩ : ∃ q, t ^ 2 = 24 * q + 1 := ⟨t ^ 2 / 24, by omega⟩
  refine ⟨(q : ℤ), ?_⟩
  have : (t : ℤ) ^ 2 = 24 * (q : ℤ) + 1 := by exact_mod_cast hq
  linarith

/-- `P'^t = (d/t) P`, the arithmetic heart of the character formula. -/
lemma petVal_conj_pow (ht2 : ¬ 2 ∣ t) (ht3 : ¬ 3 ∣ t) (γ : SL(2, ℤ)) (h : (t : ℤ) ∣ γ 1 0)
    (hc : Odd (γ 1 0)) (hc0 : 0 < γ 1 0) :
    petVal (conjT t γ h) ^ t = (jacobiSym (γ 1 1) t : ℤ) * petVal γ := by
  obtain ⟨c₁, hc₁⟩ := h
  have ht0 : (t : ℤ) ≠ 0 := by
    intro h0
    have : t = 0 := by exact_mod_cast h0
    exact ht2 (this ▸ dvd_zero 2)
  have hdiv : γ 1 0 / (t : ℤ) = c₁ := by rw [hc₁, Int.mul_ediv_cancel_left _ ht0]
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.property
    rwa [Matrix.det_fin_two] at h
  have htodd : Odd t := Nat.odd_iff.mpr (by omega)
  have hnat : (γ 1 0).natAbs = t * c₁.natAbs := by
    rw [hc₁, Int.natAbs_mul, Int.natAbs_natCast]
  have hcop : Int.gcd (γ 1 1) (γ 1 0) = 1 := by
    apply Int.isCoprime_iff_gcd_eq_one.mp
    exact ⟨γ 0 0, -γ 0 1, by linear_combination hdet⟩
  have hJne : ∀ m : ℕ, m ∣ (γ 1 0).natAbs → jacobiSym (γ 1 1) m ^ 2 = 1 := by
    intro m hm
    apply jacobiSym.sq_one
    apply Nat.Coprime.coprime_dvd_right hm
    exact hcop
  have hJ1 : jacobiSym (γ 1 1) c₁.natAbs ^ 2 = 1 :=
    hJne _ (by rw [hnat]; exact dvd_mul_left _ _)
  have hJodd : jacobiSym (γ 1 1) c₁.natAbs ^ t = jacobiSym (γ 1 1) c₁.natAbs := by
    obtain ⟨u, hu⟩ := htodd
    rw [hu, pow_succ, pow_mul, hJ1, one_pow, one_mul]
  unfold petVal
  rw [coe_conj_00, coe_conj_01, coe_conj_10, coe_conj_11, hdiv, mul_pow, hc₁]
  have hval : ((jacobiSym (γ 1 1) c₁.natAbs : ℤ) : ℂ) ^ t = jacobiSym (γ 1 1) c₁.natAbs := by
    exact_mod_cast hJodd
  have htN : t ≠ 0 := fun h0 => ht2 (h0 ▸ dvd_zero 2)
  have hc₁0 : c₁.natAbs ≠ 0 := by
    intro h0
    have : c₁ = 0 := Int.natAbs_eq_zero.mp h0
    rw [hc₁, this, mul_zero] at hc0
    exact lt_irrefl _ hc0
  have hmul : jacobiSym (γ 1 1) ((t : ℤ) * c₁).natAbs =
      jacobiSym (γ 1 1) t * jacobiSym (γ 1 1) c₁.natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_natCast, jacobiSym.mul_right' _ htN hc₁0]
  rw [hval, hmul, e24_pow]
  have hsq : (24 : ℤ) ∣ (t : ℤ) ^ 2 - 1 := int_sq_sub_one ht2 ht3
  have hexp : e24 ((t : ℤ) * petE (γ 0 0) ((t : ℤ) * γ 0 1) c₁ (γ 1 1)) =
      e24 (petE (γ 0 0) (γ 0 1) ((t : ℤ) * c₁) (γ 1 1)) := by
    apply e24_eq_of_dvd
    obtain ⟨u, hu⟩ := hsq
    refine ⟨γ 0 1 * γ 1 1 * u, ?_⟩
    unfold petE
    linear_combination (γ 0 1 * γ 1 1) * hu
  rw [hexp]
  have hJtC : ((jacobiSym (γ 1 1) t : ℤ) : ℂ) ^ 2 = 1 := by
    exact_mod_cast hJne t (by rw [hnat]; exact dvd_mul_right _ _)
  push_cast
  rw [show ((jacobiSym (γ 1 1) t : ℤ) : ℂ) * (((jacobiSym (γ 1 1) t : ℤ) : ℂ) *
      ((jacobiSym (γ 1 1) c₁.natAbs : ℤ) : ℂ) * e24 (petE (γ 0 0) (γ 0 1) ((t : ℤ) * c₁) (γ 1 1))) =
      ((jacobiSym (γ 1 1) t : ℤ) : ℂ) ^ 2 * (((jacobiSym (γ 1 1) c₁.natAbs : ℤ) : ℂ) *
        e24 (petE (γ 0 0) (γ 0 1) ((t : ℤ) * c₁) (γ 1 1))) by ring, hJtC, one_mul]

/-- `P^24 = 1`. -/
lemma petVal_pow_24 (γ : SL(2, ℤ)) (hc0 : γ 1 0 ≠ 0) : petVal γ ^ 24 = 1 := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.property
    rwa [Matrix.det_fin_two] at h
  have hcop : Int.gcd (γ 1 1) (γ 1 0) = 1 := by
    apply Int.isCoprime_iff_gcd_eq_one.mp
    exact ⟨γ 0 0, -γ 0 1, by linear_combination hdet⟩
  have hJ : jacobiSym (γ 1 1) (γ 1 0).natAbs ^ 2 = 1 := jacobiSym.sq_one hcop
  have hJC : ((jacobiSym (γ 1 1) (γ 1 0).natAbs : ℤ) : ℂ) ^ 2 = 1 := by exact_mod_cast hJ
  unfold petVal
  rw [mul_pow, e24_pow, show (24 : ℕ) = 2 * 12 by norm_num, pow_mul, hJC, one_pow, one_mul]
  have : e24 (((2 * 12 : ℕ) : ℤ) * petE (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) = e24 0 :=
    e24_eq_of_dvd ⟨petE (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1), by push_cast; ring⟩
  rw [this]
  simp [e24]

/-- The eta product `η(tz)^j η(z)`. -/
def Zprod (t j : ℕ) (z : ℂ) : ℂ := η (t * z) ^ j * η z

/-- The character law for the eta product. -/
def ZLaw (t j w : ℕ) (γ : SL(2, ℤ)) : Prop :=
  ∀ z : ℂ, 0 < z.im →
    Zprod t j (mob γ z) = (jacobiSym (γ 1 1) t : ℤ) * lin γ z ^ w * Zprod t j z

lemma sqrt_sq' {w : ℂ} (hw : w ≠ 0) : sqrt w ^ 2 = w := by
  rw [sqrt_exp_half hw, ← Complex.exp_nat_mul]
  have : ((2 : ℕ) : ℂ) * (log w / 2) = log w := by
    push_cast
    ring
  rw [this, Complex.exp_log hw]

variable {j w : ℕ}

/-- **The case of positive odd `c`.** -/
theorem zLaw_of_odd (ht2 : ¬ 2 ∣ t) (ht3 : ¬ 3 ∣ t) (htj : 24 ∣ t + j) (hjw : j + 1 = 2 * w)
    (γ : SL(2, ℤ)) (h : (t : ℤ) ∣ γ 1 0) (hc : Odd (γ 1 0)) (hc0 : 0 < γ 1 0) : ZLaw t j w γ := by
  intro z hz
  have htN : t ≠ 0 := fun h0 => ht2 (h0 ▸ dvd_zero 2)
  have htR : (0 : ℝ) < t := by exact_mod_cast Nat.pos_of_ne_zero htN
  have htz : 0 < ((t : ℂ) * z).im := by simpa using mul_pos htR hz
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.property
    rwa [Matrix.det_fin_two] at h
  -- both forms of Petersson's formula
  have hP : EtaLaw γ (petVal γ) := etaLaw_odd (γ 1 0).toNat γ
    (by rw [Int.toNat_of_nonneg hc0.le]) (by
      have := hc
      rwa [← Int.toNat_of_nonneg hc0.le, Int.odd_coe_nat] at this)
  obtain ⟨c₁, hc₁⟩ := h
  have ht0 : (t : ℤ) ≠ 0 := by exact_mod_cast htN
  have hconj : conjT t γ ⟨c₁, hc₁⟩ 1 0 = c₁ := by
    rw [coe_conj_10, hc₁, Int.mul_ediv_cancel_left _ ht0]
  have hc₁pos : 0 < c₁ := by
    have htpos : (0 : ℤ) < t := by exact_mod_cast Nat.pos_of_ne_zero htN
    rw [hc₁] at hc0
    exact (pos_iff_pos_of_mul_pos hc0).mp htpos
  have hc₁odd : Odd c₁ := by
    rw [hc₁] at hc
    exact (Int.odd_mul.mp hc).2
  have hP' : EtaLaw (conjT t γ ⟨c₁, hc₁⟩) (petVal (conjT t γ ⟨c₁, hc₁⟩)) :=
    etaLaw_odd c₁.toNat _ (by rw [hconj, Int.toNat_of_nonneg hc₁pos.le]) (by
      have := hc₁odd
      rwa [← Int.toNat_of_nonneg hc₁pos.le, Int.odd_coe_nat] at this)
  set γ' := conjT t γ ⟨c₁, hc₁⟩ with hγ'
  have hL : lin γ z ≠ 0 := denom_ne_zero' γ hz
  have h1 : η (t * mob γ z) = petVal γ' * sqrt (lin γ z) * η (t * z) := by
    rw [← mob_conj htN γ ⟨c₁, hc₁⟩ z, hP' _ htz, lin_conj htN]
  have h2 := hP z hz
  have hroot : sqrt (lin γ z) ^ j * sqrt (lin γ z) = lin γ z ^ w := by
    rw [← pow_succ, hjw, pow_mul, sqrt_sq' hL]
  -- the root of unity
  have hpow := petVal_conj_pow ht2 ht3 γ ⟨c₁, hc₁⟩ hc hc0
  have h24 := petVal_pow_24 γ' (by rw [hconj]; exact hc₁pos.ne')
  have hmain : petVal γ' ^ j * petVal γ = (jacobiSym (γ 1 1) t : ℤ) := by
    obtain ⟨u, hu⟩ := htj
    have hone : petVal γ' ^ (t + j) = 1 := by
      rw [hu, pow_mul, h24, one_pow]
    rw [pow_add, hpow] at hone
    have hcop : Int.gcd (γ 1 1) t = 1 := by
      apply Int.isCoprime_iff_gcd_eq_one.mp
      refine ⟨γ 0 0, -(γ 0 1 * c₁), ?_⟩
      rw [hc₁] at hdet
      linear_combination hdet
    have hJ : ((jacobiSym (γ 1 1) t : ℤ) : ℂ) ^ 2 = 1 := by exact_mod_cast jacobiSym.sq_one hcop
    calc petVal γ' ^ j * petVal γ
        = ((jacobiSym (γ 1 1) t : ℤ) : ℂ) ^ 2 * (petVal γ' ^ j * petVal γ) := by rw [hJ, one_mul]
      _ = ((jacobiSym (γ 1 1) t : ℤ) : ℂ) *
          (((jacobiSym (γ 1 1) t : ℤ) : ℂ) * petVal γ * petVal γ' ^ j) := by ring
      _ = _ := by rw [hone, mul_one]
  unfold Zprod
  rw [h1, h2, mul_pow, mul_pow]
  calc (petVal γ' ^ j * sqrt (lin γ z) ^ j * η (t * z) ^ j) * (petVal γ * sqrt (lin γ z) * η z)
      = (petVal γ' ^ j * petVal γ) * (sqrt (lin γ z) ^ j * sqrt (lin γ z)) *
        (η (t * z) ^ j * η z) := by ring
    _ = _ := by rw [hmain, hroot]

/-- `(-1)^w (-1/t) = 1`. -/
lemma sign_w (ht2 : ¬ 2 ∣ t) (htj : 24 ∣ t + j) (hjw : j + 1 = 2 * w) :
    (-1 : ℤ) ^ w * ZMod.χ₄ t = 1 := by
  rcases Nat.even_or_odd w with hw | hw
  · obtain ⟨u, hu⟩ := hw
    have h4 : t % 4 = 1 := by omega
    rw [Even.neg_one_pow ⟨u, hu⟩, ZMod.χ₄_nat_one_mod_four h4]
    rfl
  · obtain ⟨u, hu⟩ := hw
    have h4 : t % 4 = 3 := by omega
    rw [Odd.neg_one_pow ⟨u, hu⟩, ZMod.χ₄_nat_three_mod_four h4]
    rfl

lemma neg_entry (γ : SL(2, ℤ)) (i j : Fin 2) : (-γ) i j = -(γ i j) := by
  simp [Matrix.SpecialLinearGroup.coe_neg]

lemma mob_neg (γ : SL(2, ℤ)) (z : ℂ) : mob (-γ) z = mob γ z := by
  unfold mob
  simp only [neg_entry]
  push_cast
  rw [show -(γ 0 0 : ℂ) * z + -(γ 0 1 : ℂ) = -((γ 0 0 : ℂ) * z + γ 0 1) by ring,
    show -(γ 1 0 : ℂ) * z + -(γ 1 1 : ℂ) = -((γ 1 0 : ℂ) * z + γ 1 1) by ring, neg_div_neg_eq]

lemma lin_neg (γ : SL(2, ℤ)) (z : ℂ) : lin (-γ) z = -lin γ z := by
  unfold lin
  simp only [neg_entry]
  push_cast
  ring

/-- Passage from `γ` to `-γ`. -/
lemma ZLaw.neg (ht2 : ¬ 2 ∣ t) (htj : 24 ∣ t + j) (hjw : j + 1 = 2 * w) {γ : SL(2, ℤ)}
    (h : ZLaw t j w γ) : ZLaw t j w (-γ) := by
  intro z hz
  have htodd : Odd t := Nat.odd_iff.mpr (by omega)
  rw [mob_neg, lin_neg, h z hz, neg_entry, jacobiSym.neg _ htodd, neg_pow]
  have hs := sign_w ht2 htj hjw
  have hsC : ((-1 : ℂ)) ^ w * ((ZMod.χ₄ t : ℤ) : ℂ) = 1 := by exact_mod_cast hs
  push_cast
  calc ((jacobiSym (γ 1 1) t : ℤ) : ℂ) * lin γ z ^ w * Zprod t j z
      = ((-1 : ℂ) ^ w * ((ZMod.χ₄ t : ℤ) : ℂ)) * ((jacobiSym (γ 1 1) t : ℤ) : ℂ) * lin γ z ^ w *
        Zprod t j z := by rw [hsC, one_mul]
    _ = _ := by ring

lemma ZLaw.of_neg (ht2 : ¬ 2 ∣ t) (htj : 24 ∣ t + j) (hjw : j + 1 = 2 * w) {γ : SL(2, ℤ)}
    (h : ZLaw t j w (-γ)) : ZLaw t j w γ := by
  simpa using h.neg ht2 htj hjw

/-- The law for odd `c` of either sign. -/
lemma zLaw_of_odd' (ht2 : ¬ 2 ∣ t) (ht3 : ¬ 3 ∣ t) (htj : 24 ∣ t + j) (hjw : j + 1 = 2 * w)
    (γ : SL(2, ℤ)) (h : (t : ℤ) ∣ γ 1 0) (hc : Odd (γ 1 0)) : ZLaw t j w γ := by
  have hne : γ 1 0 ≠ 0 := fun h0 => by simp [h0] at hc
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · apply ZLaw.of_neg ht2 htj hjw
    apply zLaw_of_odd ht2 ht3 htj hjw
    · rw [neg_entry]
      exact (dvd_neg).mpr h
    · rw [neg_entry]
      exact hc.neg
    · rw [neg_entry]
      exact neg_pos.mpr hneg
  · exact zLaw_of_odd ht2 ht3 htj hjw γ h hc hpos

/-- The matrix `[1 0; t 1]`. -/
def lowT (t : ℕ) : SL(2, ℤ) := ⟨!![1, 0; (t : ℤ), 1], by simp [Matrix.det_fin_two_of]⟩

lemma lowT_mul_00 (γ : SL(2, ℤ)) : (γ * lowT t) 0 0 = γ 0 0 + γ 0 1 * t := by
  simp [lowT, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
lemma lowT_mul_01 (γ : SL(2, ℤ)) : (γ * lowT t) 0 1 = γ 0 1 := by
  simp [lowT, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
lemma lowT_mul_10 (γ : SL(2, ℤ)) : (γ * lowT t) 1 0 = γ 1 0 + γ 1 1 * t := by
  simp [lowT, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
lemma lowT_mul_11 (γ : SL(2, ℤ)) : (γ * lowT t) 1 1 = γ 1 1 := by
  simp [lowT, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

/-- **The character of the eta product on all of Γ₀(t).** -/
theorem zLaw (ht2 : ¬ 2 ∣ t) (ht3 : ¬ 3 ∣ t) (htj : 24 ∣ t + j) (hjw : j + 1 = 2 * w)
    (γ : SL(2, ℤ)) (h : (t : ℤ) ∣ γ 1 0) : ZLaw t j w γ := by
  rcases Int.even_or_odd (γ 1 0) with hce | hco
  swap
  · exact zLaw_of_odd' ht2 ht3 htj hjw γ h hco
  have htN : t ≠ 0 := fun h0 => ht2 (h0 ▸ dvd_zero 2)
  have htodd : Odd (t : ℤ) := by
    have : Odd t := Nat.odd_iff.mpr (by omega)
    exact_mod_cast this
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.property
    rwa [Matrix.det_fin_two] at h
  have hdo : Odd (γ 1 1) := by
    by_contra hd
    rw [Int.not_odd_iff_even] at hd
    have : Even (γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0) :=
      (hd.mul_left _).sub (hce.mul_left _)
    rw [hdet] at this
    exact absurd this (by decide)
  have hl : ZLaw t j w (lowT t) := by
    apply zLaw_of_odd' ht2 ht3 htj hjw
    · exact dvd_rfl
    · exact htodd
  have hγ' : ZLaw t j w (γ * lowT t) := by
    apply zLaw_of_odd' ht2 ht3 htj hjw
    · rw [lowT_mul_10]
      exact dvd_add h (dvd_mul_left _ _)
    · rw [lowT_mul_10]
      exact hce.add_odd (hdo.mul htodd)
  intro y hy
  let g : SL(2, ℤ) := ⟨!![1, 0; -(t : ℤ), 1], by simp [Matrix.det_fin_two_of]⟩
  have hD : lin g y ≠ 0 := denom_ne_zero' g hy
  let z : ℂ := mob g y
  have hz : 0 < z.im := mob_im_pos g hy
  have hDe : lin g y = -(t : ℂ) * y + 1 := by
    simp [lin, g]
  have hze : z = y / (-(t : ℂ) * y + 1) := by
    simp [z, mob, g]
  have hL : lin (lowT t) z ≠ 0 := denom_ne_zero' _ hz
  have hLe : lin (lowT t) z = (t : ℂ) * z + 1 := by
    simp [lin, lowT]
  have hD' : -(t : ℂ) * y + 1 ≠ 0 := by rwa [hDe] at hD
  have hL' : (t : ℂ) * z + 1 = 1 / (-(t : ℂ) * y + 1) := by
    rw [hze, eq_div_iff hD', add_mul, mul_assoc, div_mul_cancel₀ _ hD']
    ring
  have hm : mob (lowT t) z = z / ((t : ℂ) * z + 1) := by
    simp [mob, lowT]
  have hmob : mob (lowT t) z = y := by
    rw [hm, hL', hze, one_div, div_inv_eq_mul, div_mul_cancel₀ _ hD']
  have hE : (t : ℂ) * z + 1 ≠ 0 := by rwa [hLe] at hL
  have hexp : ∀ A B : ℂ, (A * (z / ((t : ℂ) * z + 1)) + B) * ((t : ℂ) * z + 1) =
      A * z + B * ((t : ℂ) * z + 1) := by
    intro A B
    rw [add_mul, mul_assoc, div_mul_cancel₀ _ hE]
  have hlinmul : lin (γ * lowT t) z = lin γ y * lin (lowT t) z := by
    rw [← hmob, hm, hLe]
    unfold lin
    rw [lowT_mul_10, lowT_mul_11, hexp]
    push_cast
    ring
  have hmobmul : mob (γ * lowT t) z = mob γ y := by
    have hX := denom_ne_zero' (γ * lowT t) hz
    have hnum : ((γ 0 0 : ℂ) * y + γ 0 1) * ((t : ℂ) * z + 1) =
        ((γ * lowT t) 0 0 : ℂ) * z + ((γ * lowT t) 0 1 : ℂ) := by
      rw [lowT_mul_00, lowT_mul_01, ← hmob, hm, hexp]
      push_cast
      ring
    have hdn : lin γ y * ((t : ℂ) * z + 1) = lin (γ * lowT t) z := by rw [hlinmul, hLe]
    unfold mob
    change (((γ * lowT t) 0 0 : ℂ) * z + ((γ * lowT t) 0 1 : ℂ)) / lin (γ * lowT t) z =
      ((γ 0 0 : ℂ) * y + γ 0 1) / lin γ y
    rw [← hnum, ← hdn, mul_div_mul_right _ _ hE]
  have h1 := hγ' z hz
  have h2 := hl z hz
  rw [hmobmul, lowT_mul_11, hlinmul, mul_pow] at h1
  rw [hmob] at h2
  have hone : jacobiSym (lowT t 1 1) t = 1 := by
    change jacobiSym 1 t = 1
    exact jacobiSym.one_left t
  rw [hone] at h2
  rw [h1, h2]
  push_cast
  ring

end

end RamanujanTau.ThetaLift
