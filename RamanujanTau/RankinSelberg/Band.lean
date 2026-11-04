/-
# The invariant `G(z) = |Δ(z)|² (Im z)¹²` and a Farey lower bound on horocycles

* `G_smul`: `G` is `SL₂(ℤ)`-invariant (Mathlib's `norm_petersson_smul`).
* `exists_band_lower`: `G ≥ m > 0` on the band `4/5 ≤ Im z ≤ 16` (compactness of
  `[0,1] × [4/5,16]`, `Δ ≠ 0`, and `T`-periodicity).
* `G_farey_lower`: for coprime `1 ≤ a ≤ c ≤ C` and `a/c − x ∈ [1/(4cC), 1/(2cC)]`, the point
  `x + i/C²` is moved into the band by an element of `SL₂(ℤ)` with bottom row `(c, −a)`,
  so `G(x + i/C²) ≥ m`.
-/
import RamanujanTau.RankinSelberg.Upper

set_option autoImplicit false

namespace RamanujanTau.RankinSelberg

open Complex ModularForm MeasureTheory Finset ModularGroup
open UpperHalfPlane hiding I
open scoped MatrixGroups Real

/-- The `SL₂(ℤ)`-invariant function `|Δ(z)|² (Im z)¹²`. -/
noncomputable def G (z : ℍ) : ℝ := ‖Δf z‖ ^ 2 * z.im ^ 12

lemma G_eq_norm_petersson (z : ℍ) : G z = ‖petersson 12 Δf Δf z‖ := by
  simp only [G, petersson, norm_mul, Complex.norm_conj, norm_zpow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos z.im_pos]
  simp only [zpow_ofNat]; ring

lemma G_smul (g : SL(2, ℤ)) (z : ℍ) : G (g • z) = G z := by
  rw [G_eq_norm_petersson, G_eq_norm_petersson]
  exact SlashInvariantFormClass.norm_petersson_smul (Γ := 𝒮ℒ)
    (f := (CuspForm.discriminant : CuspForm 𝒮ℒ 12))
    (f' := (CuspForm.discriminant : CuspForm 𝒮ℒ 12)) ⟨g, rfl⟩

lemma continuous_G : Continuous G := by
  unfold G
  exact ((ModularFormClass.holo (CuspForm.discriminant : CuspForm 𝒮ℒ 12)).continuous.norm.pow 2).mul
    (UpperHalfPlane.continuous_im.pow 12)

lemma G_pos (z : ℍ) : 0 < G z := by
  unfold G
  have h1 : Δf z ≠ 0 := by
    rw [Δf, CuspForm.coe_discriminant]; exact discriminant_ne_zero z
  have := z.im_pos
  positivity

/-- The band point `p.1 + i·max(p.2, 4/5)`. -/
noncomputable def bandPt (p : ℝ × ℝ) : ℍ :=
  ⟨(p.1 : ℂ) + (max p.2 (4 / 5) : ℝ) * I, by
    simp⟩

lemma continuous_bandPt : Continuous bandPt :=
  Continuous.upperHalfPlaneMk (by fun_prop) _

/-- **`G` is bounded below on the band** `4/5 ≤ Im z ≤ 16`. -/
theorem exists_band_lower : ∃ m : ℝ, 0 < m ∧ ∀ z : ℍ, 4 / 5 ≤ z.im → z.im ≤ 16 → m ≤ G z := by
  set K : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (4 / 5 : ℝ) 16
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hne : K.Nonempty := ⟨(0, 1), by simp [K]; norm_num⟩
  obtain ⟨p, -, hmin⟩ := hK.exists_isMinOn hne (continuous_G.comp continuous_bandPt).continuousOn
  refine ⟨G (bandPt p), G_pos _, fun z hz1 hz2 => ?_⟩
  set n : ℤ := ⌊z.re⌋
  set z' : ℍ := (T ^ (-n)) • z
  have hre : z'.re = z.re - n := by
    simp only [z', re_T_zpow_smul]; push_cast; ring
  have him : z'.im = z.im := im_T_zpow_smul _ _
  have hz' : bandPt (z'.re, z'.im) = z' := by
    ext
    simp only [bandPt, UpperHalfPlane.coe_mk]
    rw [max_eq_left (by rw [him]; exact hz1)]
    exact UpperHalfPlane.re_add_im z'
  have hmem : (z'.re, z'.im) ∈ K := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · show 0 ≤ z'.re; rw [hre]; linarith [Int.floor_le z.re]
    · show z'.re ≤ 1; rw [hre]; linarith [Int.lt_floor_add_one z.re]
    · show 4 / 5 ≤ z'.im; rw [him]; exact hz1
    · show z'.im ≤ 16; rw [him]; exact hz2
  have := hmin hmem
  simp only [Function.comp, Set.mem_setOf_eq] at this
  rw [hz'] at this
  calc G (bandPt p) ≤ G z' := this
    _ = G z := G_smul _ _

/-- **Farey step**: for coprime `1 ≤ a ≤ c ≤ C` and `a/c − x ∈ [1/(4cC), 1/(2cC)]`, the point
`x + i/C²` has an `SL₂(ℤ)`-image in the band `4/5 ≤ Im ≤ 16`. -/
theorem exists_smul_mem_band {C a c : ℕ} (hC : 1 ≤ C) (ha : 1 ≤ a) (hac : a ≤ c) (hcC : c ≤ C)
    (hcop : Nat.Coprime a c) {x : ℝ}
    (hx1 : 1 / (4 * c * C) ≤ (a : ℝ) / c - x) (hx2 : (a : ℝ) / c - x ≤ 1 / (2 * c * C))
    (hy : (0 : ℝ) < 1 / (C : ℝ) ^ 2) :
    ∃ g : SL(2, ℤ), 4 / 5 ≤ (g • hp hy x).im ∧ (g • hp hy x).im ≤ 16 := by
  have hcop' : IsCoprime (c : ℤ) (-(a : ℤ)) :=
    (Nat.isCoprime_iff_coprime.mpr hcop.symm).neg_right
  obtain ⟨g, -, hg⟩ := bottom_row_surj (R := ℤ)
    (show ![(c : ℤ), -(a : ℤ)] ∈ {cd : Fin 2 → ℤ | IsCoprime (cd 0) (cd 1)} by simpa using hcop')
  refine ⟨g, ?_⟩
  have h10 : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = c := by
    have := congrFun hg 0; simpa using this
  have h11 : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = -(a : ℤ) := by
    have := congrFun hg 1; simpa using this
  rw [ModularGroup.im_smul_eq_div_normSq, hp_im, ModularGroup.denom_apply, h10, h11]
  have hden : Complex.normSq (((c : ℤ) : ℂ) * (hp hy x : ℂ) + ((-(a : ℤ) : ℤ) : ℂ)) =
      ((c : ℝ) * x - a) ^ 2 + ((c : ℝ) * (1 / (C : ℝ) ^ 2)) ^ 2 := by
    rw [hp_coe]
    generalize (1 / (C : ℝ) ^ 2) = t
    rw [Complex.normSq_apply]
    simp; ring
  rw [hden]
  have hc0 : (1 : ℝ) ≤ c := by exact_mod_cast ha.trans hac
  have hCr : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hcCr : (c : ℝ) ≤ C := by exact_mod_cast hcC
  set d : ℝ := (a : ℝ) / c - x with hd
  have hcx : (c : ℝ) * x - a = -(c * d) := by
    rw [hd]; field_simp; ring
  rw [hcx]
  -- `c²d² ∈ [1/(16C²), 1/(4C²)]` and `c²/C⁴ ≤ 1/C²`
  have hcd1 : 1 / (4 * C) ≤ c * d := by
    have := mul_le_mul_of_nonneg_left hx1 (by linarith : (0 : ℝ) ≤ c)
    rwa [show (c : ℝ) * (1 / (4 * c * C)) = 1 / (4 * C) by field_simp] at this
  have hcd2 : c * d ≤ 1 / (2 * C) := by
    have := mul_le_mul_of_nonneg_left hx2 (by linarith : (0 : ℝ) ≤ c)
    rwa [show (c : ℝ) * (1 / (2 * c * C)) = 1 / (2 * C) by field_simp] at this
  have hC0 : (0 : ℝ) < C := by linarith
  have hD1 : 1 / (16 * (C : ℝ) ^ 2) ≤ (-(c * d)) ^ 2 + ((c : ℝ) * (1 / (C : ℝ) ^ 2)) ^ 2 := by
    have h0 : 0 ≤ 1 / (4 * (C : ℝ)) := by positivity
    have : (1 / (4 * (C : ℝ))) ^ 2 ≤ (c * d) ^ 2 := pow_le_pow_left₀ h0 hcd1 2
    have e : (1 / (4 * (C : ℝ))) ^ 2 = 1 / (16 * (C : ℝ) ^ 2) := by field_simp; ring
    nlinarith [sq_nonneg ((c : ℝ) * (1 / (C : ℝ) ^ 2))]
  have hD2 : (-(c * d)) ^ 2 + ((c : ℝ) * (1 / (C : ℝ) ^ 2)) ^ 2 ≤ 5 / (4 * (C : ℝ) ^ 2) := by
    have h0 : 0 ≤ c * d := le_trans (by positivity) hcd1
    have h1 : (c * d) ^ 2 ≤ (1 / (2 * (C : ℝ))) ^ 2 := pow_le_pow_left₀ h0 hcd2 2
    have h2 : ((c : ℝ) * (1 / (C : ℝ) ^ 2)) ^ 2 ≤ (1 / (C : ℝ)) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      rw [show (c : ℝ) * (1 / (C : ℝ) ^ 2) = (c / C) * (1 / C) by field_simp]
      calc (c : ℝ) / C * (1 / C) ≤ 1 * (1 / C) := by
            gcongr; rw [div_le_one hC0]; exact hcCr
        _ = 1 / C := one_mul _
    have e1 : (1 / (2 * (C : ℝ))) ^ 2 = 1 / (4 * (C : ℝ) ^ 2) := by field_simp; ring
    have e2 : (1 / (C : ℝ)) ^ 2 = 4 / (4 * (C : ℝ) ^ 2) := by field_simp
    rw [neg_sq]; rw [e1] at h1; rw [e2] at h2
    have : 1 / (4 * (C : ℝ) ^ 2) + 4 / (4 * (C : ℝ) ^ 2) = 5 / (4 * (C : ℝ) ^ 2) := by ring
    linarith
  set D := (-(c * d)) ^ 2 + ((c : ℝ) * (1 / (C : ℝ) ^ 2)) ^ 2
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hD1
  constructor
  · rw [le_div_iff₀ hDpos]
    calc 4 / 5 * D ≤ 4 / 5 * (5 / (4 * (C : ℝ) ^ 2)) := by gcongr
      _ = 1 / (C : ℝ) ^ 2 := by field_simp
  · rw [div_le_iff₀ hDpos]
    calc 1 / (C : ℝ) ^ 2 = 16 * (1 / (16 * (C : ℝ) ^ 2)) := by field_simp
      _ ≤ 16 * D := by gcongr

/-- **Farey lower bound**: `|Δ(x + i/C²)|² ≥ m C²⁴` on each Farey interval. -/
theorem normSq_farey_lower {m : ℝ} (hm : ∀ z : ℍ, 4 / 5 ≤ z.im → z.im ≤ 16 → m ≤ G z)
    {C a c : ℕ} (hC : 1 ≤ C) (ha : 1 ≤ a) (hac : a ≤ c) (hcC : c ≤ C)
    (hcop : Nat.Coprime a c) {x : ℝ}
    (hx1 : 1 / (4 * c * C) ≤ (a : ℝ) / c - x) (hx2 : (a : ℝ) / c - x ≤ 1 / (2 * c * C))
    (hy : (0 : ℝ) < 1 / (C : ℝ) ^ 2) :
    m * (C : ℝ) ^ 24 ≤ ‖Δf (hp hy x)‖ ^ 2 := by
  obtain ⟨g, h1, h2⟩ := exists_smul_mem_band hC ha hac hcC hcop hx1 hx2 hy
  have hG := (hm _ h1 h2).trans_eq (G_smul g (hp hy x))
  unfold G at hG
  rw [hp_im] at hG
  have hC0 : (0 : ℝ) < C := by exact_mod_cast hC
  have e : (1 / (C : ℝ) ^ 2) ^ 12 = 1 / (C : ℝ) ^ 24 := by rw [div_pow, ← pow_mul]; simp
  rw [e, mul_one_div, le_div_iff₀ (by positivity)] at hG
  exact hG

end RamanujanTau.RankinSelberg
