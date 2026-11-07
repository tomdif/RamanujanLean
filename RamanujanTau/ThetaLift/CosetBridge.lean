import RamanujanTau.ThetaLift.ModularDomain

/-!
# Cosets and lattice points

The cosets of the translations in the image of `Γ₀(N)` correspond to coprime bottom rows up to sign. A
nonzero `g` and a coset give the point `(a,m) = (-gd, gc/N)`, which is every point with `a` prime to `N`.
-/

set_option autoImplicit false

namespace RamanujanTau.ThetaLift
open UpperHalfPlane Set
open scoped MatrixGroups Modular

noncomputable section

variable (N : ℕ)

/-- The congruence subgroup. -/
abbrev gN : Subgroup SL(2, ℤ) := CongruenceSubgroup.Gamma0 N

lemma T_mem : ModularGroup.T ∈ gN N := by
  rw [CongruenceSubgroup.Gamma0_mem]
  simp [ModularGroup.T]

lemma neg_one_mem : (-1 : SL(2, ℤ)) ∈ gN N := by
  rw [CongruenceSubgroup.Gamma0_mem]
  simp

lemma dvd_of_mem {γ : SL(2, ℤ)} (h : γ ∈ gN N) : (N : ℤ) ∣ γ 1 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp h)

lemma mem_of_dvd {γ : SL(2, ℤ)} (h : (N : ℤ) ∣ γ 1 0) : γ ∈ gN N :=
  CongruenceSubgroup.Gamma0_mem.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h)

/-- The quotient of the image of `Γ₀(N)` by the translations. -/
abbrev cosetN : Type := pSub (gN N) ⧸ tSub (T_mem N)

variable {N}

/-- A matrix representing the inverse of a coset representative. -/
def gamR (r : cosetN N) : SL(2, ℤ) := ((r.out⁻¹ : pSub (gN N))).2.choose

lemma gamR_mem (r : cosetN N) : gamR r ∈ gN N := ((r.out⁻¹ : pSub (gN N))).2.choose_spec.1

lemma pG_gamR (r : cosetN N) : pG (gamR r) = ((r.out⁻¹ : pSub (gN N)) : Equiv.Perm ℍ) :=
  ((r.out⁻¹ : pSub (gN N))).2.choose_spec.2

lemma smul_gamR (r : cosetN N) (z : ℍ) : (r.out⁻¹ : pSub (gN N)) • z = gamR r • z := by
  rw [smul_pSub, ← pG_gamR]
  rfl

lemma bottom_coprime (γ : SL(2, ℤ)) : IsCoprime (γ 1 0) (γ 1 1) := by
  have h := γ.property
  rw [Matrix.det_fin_two] at h
  exact ⟨-γ 0 1, γ 0 0, by linear_combination h⟩

/-- The bottom-left entry of `γ δ⁻¹`. -/
lemma mul_inv_10 (γ δ : SL(2, ℤ)) : (γ * δ⁻¹) 1 0 = γ 1 0 * δ 1 1 - γ 1 1 * δ 1 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two]
  simp
  ring

/-- The translations are the elements with `c = 0`. -/
lemma mem_tSub_of {x : pSub (gN N)} {e : SL(2, ℤ)} (hx : (x : Equiv.Perm ℍ) = pG e) (he : e 1 0 = 0) :
    x ∈ tSub (T_mem N) := by
  obtain ⟨n, hn⟩ := ModularGroup.exists_eq_T_zpow_of_c_eq_zero he
  refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
  apply Subtype.ext
  rw [hx]
  ext z
  have h1 : (((tEl (T_mem N)) ^ n : pSub (gN N)) : Equiv.Perm ℍ) = pG (ModularGroup.T ^ n) := by
    simp [tEl, map_zpow]
  rw [h1]
  exact congrArg UpperHalfPlane.coe (hn z).symm

/-- Equal bottom rows up to proportionality give equal cosets. -/
lemma coset_eq_of_rows {r r' : cosetN N}
    (h : gamR r 1 0 * gamR r' 1 1 = gamR r 1 1 * gamR r' 1 0) : r = r' := by
  have hmem : ((r.out⁻¹ * r'.out : pSub (gN N))) ∈ tSub (T_mem N) := by
    refine mem_tSub_of (e := gamR r * (gamR r')⁻¹) ?_ ?_
    · rw [map_mul, map_inv, pG_gamR, pG_gamR]
      simp
    · rw [mul_inv_10, h]
      ring
  have := QuotientGroup.eq.mpr hmem
  simpa using this

/-- The lattice point of a coset and a nonzero integer. -/
def bMap (r : cosetN N) (g : {g : ℤ // g ≠ 0}) : ℤ × ℤ :=
  (-(g : ℤ) * gamR r 1 1, (g : ℤ) * (gamR r 1 0 / N))

lemma gamR_mul_div (hN : 0 < N) (r : cosetN N) : (N : ℤ) * (gamR r 1 0 / N) = gamR r 1 0 :=
  Int.mul_ediv_cancel' (dvd_of_mem N (gamR_mem r))

/-- **The map to lattice points is injective.** -/
theorem bMap_inj (hN : 0 < N) : Function.Injective fun p : cosetN N × {g : ℤ // g ≠ 0} => bMap p.1 p.2 := by
  rintro ⟨r, g⟩ ⟨r', g'⟩ h
  simp only [bMap, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hNZ : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hc : (g : ℤ) * gamR r 1 0 = g' * gamR r' 1 0 := by
    rw [← gamR_mul_div hN r, ← gamR_mul_div hN r']
    linear_combination (N : ℤ) * h2
  have hd : (g : ℤ) * gamR r 1 1 = g' * gamR r' 1 1 := by linear_combination -h1
  have hg := g.2
  have hrows : gamR r 1 0 * gamR r' 1 1 = gamR r 1 1 * gamR r' 1 0 := by
    apply mul_left_cancel₀ hg
    linear_combination gamR r' 1 1 * hc - gamR r' 1 0 * hd
  have hr : r = r' := coset_eq_of_rows hrows
  subst hr
  have hcop := bottom_coprime (gamR r)
  obtain ⟨u, v, huv⟩ := hcop
  have hgg : (g : ℤ) = g' := by
    linear_combination u * hc + v * hd - ((g : ℤ) - g') * huv
  have hg2 : g = g' := Subtype.ext hgg
  rw [hg2]

/-- Two matrices acting the same differ by a sign. -/
lemma eq_or_neg_of_pG {a b : SL(2, ℤ)} (h : pG a = pG b) : a = b ∨ a = -b := by
  let z0 : ℍ := ⟨2 * Complex.I, by simp⟩
  have hz0 : z0 ∈ 𝒟ᵒ := by
    constructor
    · change 1 < Complex.normSq (2 * Complex.I)
      simp [Complex.normSq_apply]
      norm_num
    · change |((2 : ℂ) * Complex.I).re| < 1 / 2
      simp
  have he : (b⁻¹ * a) • z0 = z0 := by
    rw [mul_smul, ← pG_apply a, h, pG_apply, inv_smul_smul]
  have hmem : (b⁻¹ * a) • z0 ∈ 𝒟 := by
    rw [he]
    exact ModularGroup.fdo_subset_fd hz0
  rcases ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd hz0 hmem with h1 | h1
  · left
    exact (inv_mul_eq_one.mp h1).symm
  · right
    calc a = b * (b⁻¹ * a) := (mul_inv_cancel_left _ _).symm
      _ = -b := by rw [h1, mul_neg, mul_one]

/-- A matrix with prescribed coprime bottom row. -/
lemma exists_bottom {c d : ℤ} (h : IsCoprime c d) : ∃ δ : SL(2, ℤ), δ 1 0 = c ∧ δ 1 1 = d := by
  obtain ⟨s, t, hst⟩ := h
  refine ⟨⟨!![t, -s; c, d], ?_⟩, rfl, rfl⟩
  rw [Matrix.det_fin_two_of]
  linear_combination hst

/-- The bottom row is unchanged by a translation. -/
lemma T_zpow_mul_bottom (n : ℤ) (δ : SL(2, ℤ)) :
    (ModularGroup.T ^ n * δ) 1 0 = δ 1 0 ∧ (ModularGroup.T ^ n * δ) 1 1 = δ 1 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **The map to lattice points covers every point with `a` prime to `N`.** -/
theorem bMap_surj (hN : 0 < N) {a m : ℤ} (ha : IsCoprime a (N : ℤ)) (h0 : (a, m) ≠ (0, 0)) :
    ∃ (r : cosetN N) (g : {g : ℤ // g ≠ 0}), bMap r g = (a, m) := by
  have hNZ : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hgpos : 0 < Int.gcd a m := by
    apply Nat.pos_of_ne_zero
    intro hz
    have := Int.gcd_eq_zero_iff.mp hz
    exact h0 (by rw [this.1, this.2])
  set g₀ : ℤ := (Int.gcd a m : ℤ) with hg₀
  have hg0 : g₀ ≠ 0 := by
    rw [hg₀]
    exact_mod_cast hgpos.ne'
  obtain ⟨a₁, ha₁⟩ : g₀ ∣ a := Int.gcd_dvd_left a m
  obtain ⟨m₁, hm₁⟩ : g₀ ∣ m := Int.gcd_dvd_right a m
  have hcop1 : IsCoprime a₁ m₁ := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h := Int.gcd_div_gcd_div_gcd (i := a) (j := m) hgpos
    have e1 : a / (Int.gcd a m : ℤ) = a₁ := by
      rw [← hg₀, ha₁, Int.mul_ediv_cancel_left _ hg0]
    have e2 : m / (Int.gcd a m : ℤ) = m₁ := by
      rw [← hg₀, hm₁, Int.mul_ediv_cancel_left _ hg0]
    rwa [e1, e2] at h
  have hcop2 : IsCoprime a₁ (N : ℤ) := by
    rw [ha₁] at ha
    exact ha.of_mul_left_right
  have hcop : IsCoprime ((N : ℤ) * m₁) (-a₁) :=
    ((hcop2.mul_right hcop1).symm).neg_right
  obtain ⟨δ, hδc, hδd⟩ := exists_bottom hcop
  have hδmem : δ ∈ gN N := mem_of_dvd N (by rw [hδc]; exact dvd_mul_right _ _)
  let x : pSub (gN N) := ⟨pG δ, δ, hδmem, rfl⟩
  let r : cosetN N := ((x⁻¹ : pSub (gN N)) : pSub (gN N) ⧸ tSub (T_mem N))
  have hrel : (r.out⁻¹ * x⁻¹ : pSub (gN N)) ∈ tSub (T_mem N) := by
    apply QuotientGroup.eq.mp
    simp [r]
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hrel
  have hperm : pG (gamR r) = pG (ModularGroup.T ^ n * δ) := by
    have h1 : (((tEl (T_mem N)) ^ n : pSub (gN N)) : Equiv.Perm ℍ) =
        ((r.out⁻¹ * x⁻¹ : pSub (gN N)) : Equiv.Perm ℍ) := congrArg Subtype.val hn
    have e1 : (((tEl (T_mem N)) ^ n : pSub (gN N)) : Equiv.Perm ℍ) = (pG ModularGroup.T) ^ n := by
      simp [tEl]
    have e2 : ((r.out⁻¹ * x⁻¹ : pSub (gN N)) : Equiv.Perm ℍ) = pG (gamR r) * (pG δ)⁻¹ := by
      rw [Subgroup.coe_mul, ← pG_gamR]
      rfl
    rw [map_mul, map_zpow, ← e1, h1, e2, inv_mul_cancel_right]
  obtain ⟨hb1, hb2⟩ := T_zpow_mul_bottom n δ
  have hdivc : ∀ e : ℤ, ((N : ℤ) * e) / N = e := fun e => Int.mul_ediv_cancel_left _ hNZ
  rcases eq_or_neg_of_pG hperm with hg | hg
  · refine ⟨r, ⟨g₀, hg0⟩, ?_⟩
    have h1 : gamR r 1 0 = (N : ℤ) * m₁ := by rw [hg, hb1, hδc]
    have h2 : gamR r 1 1 = -a₁ := by rw [hg, hb2, hδd]
    simp only [bMap]
    rw [h1, h2, hdivc]
    ext <;> simp [ha₁.symm, hm₁.symm]
  · refine ⟨r, ⟨-g₀, neg_ne_zero.mpr hg0⟩, ?_⟩
    have h1 : gamR r 1 0 = (N : ℤ) * (-m₁) := by
      rw [hg]
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
      rw [hb1, hδc]
      ring
    have h2 : gamR r 1 1 = a₁ := by
      rw [hg]
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
      rw [hb2, hδd]
      ring
    simp only [bMap]
    rw [h1, h2, hdivc]
    ext <;> simp [ha₁.symm, hm₁.symm]

end

end RamanujanTau.ThetaLift
