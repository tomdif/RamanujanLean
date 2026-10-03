/-
# The `m`-level base splitting

`A(x,z;q) = θ(z;q)·Σ_s μ_s A(X_s,Z*_s;Q)/θ(Z*_s;Q) − (theta corrections)`, `Q = q^{n²}`:
`split_A` plus change of `z` in base `Q` plus the elementary `n`-dissection of `θ(z;q)`.
-/
import RamanujanTau.ALTheta

set_option autoImplicit false

namespace ALz
open HahnSeries Finset

section ThetaDissect
variable {N : ℕ} (hN : 1 ≤ N)
include hN

/-- quasi-periodicity, `s` steps: `θ(q^s y) = (−1)^s q^{−C(s,2)·…} y^{−s} θ(y)`, in the form
`θ(q^s y) = mono(−N·C(s+1,2) + … )`; we state it as the reindexing `k ↦ k + s`. -/
theorem θ_qshift (e : ℤ) {c : ℂ} (hc : c ≠ 0) (s : ℤ) :
    θ hN (e + N * s) c = mono (-(N * c2 (s + 1)) - e * s + N * s) ((-1) ^ s * c ^ (-s)) * θ hN e c := by
  refine hsum_reindex' (thF hN e c) (thF hN (e + N * s) c) (Equiv.addRight (-s)) _ fun k => ?_
  simp only [sv, thF_apply, thT, Equiv.coe_addRight, mono_mul]
  congr 1
  · unfold thE
    have h1 := two_c2 (k + -s); have h2 := two_c2 k; have h3 := two_c2 (s + 1)
    nlinarith
  · unfold thC
    rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_add₀ hc, zpow_neg, zpow_neg]
    rw [show ((-1 : ℂ) ^ s)⁻¹ = (-1) ^ s by rw [← inv_zpow, inv_neg, inv_one]]
    ring

end ThetaDissect


section Dissect1
variable (n : ℕ) (hn : 0 < n)
include hn

/-- `k ↦ (ρ, m)` with `k = n m − ρ`, `0 ≤ ρ < n`. -/
def splitEquiv1 : ℤ ≃ Fin n × ℤ where
  toFun k := (⟨((-k) % n).toNat, by
      have h1 := Int.emod_nonneg (-k) (show (n : ℤ) ≠ 0 by omega)
      have h2 := Int.emod_lt_of_pos (-k) (show (0 : ℤ) < n by omega)
      omega⟩, (k + (-k) % n) / n)
  invFun p := n * p.2 - (p.1 : ℕ)
  left_inv k := by
    have hn' : (n : ℤ) ≠ 0 := by omega
    have h1 := Int.emod_nonneg (-k) hn'
    have hd : (n : ℤ) ∣ k + (-k) % n := by
      rw [Int.dvd_iff_emod_eq_zero, Int.add_emod, Int.emod_emod_of_dvd _ (dvd_refl _),
        ← Int.add_emod, add_neg_cancel, Int.zero_emod]
    simp only
    rw [Int.mul_ediv_cancel' hd, Int.toNat_of_nonneg h1]; ring
  right_inv p := by
    obtain ⟨ρ, m⟩ := p
    have hn' : (n : ℤ) ≠ 0 := by omega
    have hρ : ((ρ : ℕ) : ℤ) < n := by exact_mod_cast ρ.2
    have e1 : (-(n * m - (ρ : ℕ) : ℤ)) % n = (ρ : ℕ) := by
      rw [show -(n * m - ((ρ : ℕ) : ℤ)) = (ρ : ℕ) + n * (-m) by ring, Int.add_mul_emod_self_left,
        Int.emod_eq_of_lt (by positivity) hρ]
    simp only [Prod.mk.injEq, e1, Int.toNat_natCast]
    refine ⟨trivial, ?_⟩
    rw [show (n : ℤ) * m - (ρ : ℕ) + (ρ : ℕ) = n * m by ring, Int.mul_ediv_cancel_left _ hn']

end Dissect1

section Dissect
variable {N : ℕ} (hN : 1 ≤ N) (n : ℕ) (hn : 0 < n)
include hN hn

/-- **the `n`-dissection of a theta function**:
`θ(y;q) = Σ_{ρ<n} (−1)^ρ q^{C(−ρ,2)} y^{−ρ} θ((−1)^{n+1} q^{C(n,2)−nρ} yⁿ; q^{n²})`. -/
theorem θ_dissect (e : ℤ) {c : ℂ} (hc : c ≠ 0) :
    θ hN e c = ∑ ρ : Fin n, mono (N * c2 (-(ρ : ℕ) : ℤ) - e * (ρ : ℕ)) ((-1) ^ (-(ρ : ℕ) : ℤ) * c ^ (-(ρ : ℕ) : ℤ)) *
      θ (hN' hN n hn) (N * c2 n - N * n * (ρ : ℕ) + n * e) ((-1) ^ (n + 1) * c ^ n) := by
  set S := SummableFamily.Equiv (splitEquiv1 n hn) (thF hN e c)
  have h1 : θ hN e c = hs (rowFam S) := by
    rw [hs_rowFam, hs_eq, SummableFamily.hsum_equiv]; rfl
  rw [h1, hs_fintype]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [rowFam_apply]
  refine hsum_reindex' _ _ (Equiv.refl _) _ fun m => ?_
  simp only [sv, Equiv.refl_apply, row_apply, S, SummableFamily.Equiv_toFun, thF_apply, thT, mono_mul]
  rw [show (splitEquiv1 n hn).symm (ρ, m) = n * m - (ρ : ℕ) from rfl]
  congr 1
  · unfold thE
    have h0 := two_c2 ((n : ℤ) * m - (ρ : ℕ)); have h1 := two_c2 (n : ℤ)
    have h2 := two_c2 (-((ρ : ℕ) : ℤ)); have h3 := two_c2 m
    have : (2 : ℤ) * ((N : ℤ) * c2 (n * m - (ρ : ℕ)) + e * (n * m - (ρ : ℕ))) =
        2 * ((N : ℤ) * c2 (-((ρ : ℕ) : ℤ)) - e * (ρ : ℕ) +
          (((N * n * n : ℕ) : ℤ) * c2 m + (N * c2 n - N * n * (ρ : ℕ) + n * e) * m)) := by
      push_cast
      linear_combination (N : ℤ) * h0 - (N : ℤ) * m * h1 - (N : ℤ) * h2 - (N : ℤ) * n ^ 2 * h3
    omega
  · unfold thC
    have hm1 : ((-1 : ℂ)) ≠ 0 := by norm_num
    rw [show (n : ℤ) * m - (ρ : ℕ) = n * m + -((ρ : ℕ) : ℤ) by ring, zpow_add₀ hm1, zpow_add₀ hc,
      zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, mul_zpow]
    have e1 : ((-1 : ℂ) ^ (n + 1)) ^ m * (-1) ^ m = ((-1) ^ n) ^ m := by
      rw [← mul_zpow]; congr 1; ring
    rw [← e1]; ring_nf

end Dissect


section Coef
variable {N : ℕ} (hN : 1 ≤ N) (n : ℕ) (hn : 0 < n)
include hN hn

/-- the `ρ`-sum of the split prefactors times `θ(Z_{ρ,s})` is a monomial times `θ(z)`. -/
theorem split_coef (a β : ℤ) {cx cp : ℂ} (hx : cx ≠ 0) (hp : cp ≠ 0) (s : Fin n) :
    ∑ ρ : Fin n, mono (spE (N := N) a β ρ s) (spC cx cp ρ s) *
        θ (hN' hN n hn) (spB (N := N) n β ρ s) (spCP n cp)
      = mono (a * (s : ℕ) - N * c2 ((s : ℕ) + 1)) ((-1) ^ ((s : ℕ) : ℤ) * cx ^ ((s : ℕ) : ℤ)) * θ hN β cp := by
  have hd := θ_dissect hN n hn (β + N * (s : ℕ)) hp
  have hq := θ_qshift hN β hp ((s : ℕ) : ℤ)
  rw [hq] at hd
  have key : ∀ ρ : Fin n, mono (spE (N := N) a β ρ s) (spC cx cp ρ s) *
      θ (hN' hN n hn) (spB (N := N) n β ρ s) (spCP n cp) =
      mono ((a + β - N) * (s : ℕ)) ((cx * cp) ^ ((s : ℕ) : ℤ)) *
        (mono (N * c2 (-(ρ : ℕ) : ℤ) - (β + N * (s : ℕ)) * (ρ : ℕ)) ((-1) ^ (-(ρ : ℕ) : ℤ) * cp ^ (-(ρ : ℕ) : ℤ)) *
          θ (hN' hN n hn) (N * c2 n - N * n * (ρ : ℕ) + n * (β + N * (s : ℕ))) ((-1) ^ (n + 1) * cp ^ n)) := by
    intro ρ
    rw [← mul_assoc, mono_mul]
    unfold spE spC spB spCP
    congr 2
    · ring
    · ring
    · ring
  rw [Finset.sum_congr rfl fun ρ _ => key ρ, ← Finset.mul_sum, ← hd, ← mul_assoc, mono_mul]
  congr 2
  · ring
  · have h1 : cp ^ ((s : ℕ) : ℤ) * cp ^ (-((s : ℕ) : ℤ)) = 1 := by
      rw [← zpow_add₀ hp, add_neg_cancel, zpow_zero]
    rw [mul_zpow]
    linear_combination ((-1) ^ ((s : ℕ) : ℤ) * cx ^ ((s : ℕ) : ℤ)) * h1

end Coef


section Consist
variable {N : ℕ} (hN : 1 ≤ N)
include hN

/-- at interior points the cone sum and the general Appell–Lerch value agree. -/
theorem Aser_eq_Ab {a β : ℤ} (hlo : 0 < a + β) (hhi : a + β < N) {cx cp : ℂ} (hx : cx ≠ 0) (hp : cp ≠ 0) :
    Aser hN hlo hhi cx cp = Ab hN (by omega) hhi cx cp := by
  have hrow : hs (row (asF hN hlo hhi cx cp) 1) = -mono β cp * hs (geoP (a + β) (cx * cp) hlo) := by
    refine hsum_reindex' (geoP (a + β) (cx * cp) hlo) _ (Equiv.refl ℤ) _ fun j => ?_
    simp only [sv, row_apply, Equiv.refl_apply, asF_apply, geoP_apply]
    by_cases hj : 0 ≤ j
    · rw [if_pos (show cone 1 j from Or.inl ⟨le_rfl, hj⟩), if_pos hj,
        show -mono β cp = mono β (-cp) from (single_neg _ _).symm, mono_mul]
      congr 1
      · unfold asExp; simp [c2]; ring
      · unfold sgnC; rw [if_pos le_rfl]; simp
    · rw [if_neg (by unfold cone; omega), if_neg hj, mul_zero]
  have hsplit : ∀ rj, asF hN hlo hhi cx cp rj =
      (asF2 hN (by omega) hhi cx cp + (row (asF hN hlo hhi cx cp) 1).embDomain slice1) rj := by
    rintro ⟨r, j⟩
    simp only [SummableFamily.add_apply]
    by_cases hr : r = 1
    · subst hr
      have he : ((row (asF hN hlo hhi cx cp) 1).embDomain slice1) (slice1 j) = row (asF hN hlo hhi cx cp) 1 j :=
        SummableFamily.embDomain_image _ _
      change _ = _ + ((row (asF hN hlo hhi cx cp) 1).embDomain slice1) (slice1 j)
      rw [he, row_apply, asF2_apply, if_neg (fun h => h.2 rfl), zero_add]
    · rw [SummableFamily.embDomain_notin_range, add_zero, asF_apply, asF2_apply]
      · simp only [cone2, hr, ne_eq, not_false_eq_true, and_true]
      · rintro ⟨j', hj'⟩; exact hr (congrArg Prod.fst hj').symm
  have hg := hs_geoP (a + β) (cx * cp) hlo
  have hG : hs (geoP (a + β) (cx * cp) hlo) = (1 - mono (a + β) (cx * cp))⁻¹ := eq_inv_of_mul_eq_one_right hg
  rw [Aser, hsum_congr _ _ hsplit, hs_eq, SummableFamily.hsum_add, SummableFamily.hsum_embDomain,
    ← hs_eq, ← hs_eq, hrow, hG, Ab, Aser2]
  ring

end Consist


section MSplit
variable {N : ℕ} (hN : 1 ≤ N)
include hN

/-- change of `z` solved for `A(x,z₁)` (general points, auxiliary `z₀`). -/
theorem coz_solve {a b₀ b₁ : ℤ} (ha1 : -N < a) (ha2 : a < N) (hb1 : 1 ≤ a + b₀) (hb2 : a + b₀ ≤ N - 1)
    (hb3 : 1 ≤ b₀) (hb4 : b₀ ≤ N - 1) (hc0' : -N < a + b₁) (hcN : a + b₁ < N)
    {cx c₀ c₁ : ℂ} (hx : cx ≠ 0) (hc0 : c₀ ≠ 0) (hc1 : c₁ ≠ 0) (hx1 : mono a cx ≠ 1)
    (hxz1 : mono (a + b₁) (cx * c₁) ≠ 1) (hθ1 : θ hN (a + b₁) (cx * c₁) ≠ 0) :
    Ab hN hc0' hcN cx c₁ = θ hN b₁ c₁ * Ab hN (a := a) (β := b₀) (by omega) (by omega) cx c₀ / θ hN b₀ c₀
      - mono b₀ c₀ * hs (kF hN 0) * θ hN (-b₀ + b₁) (c₀⁻¹ * c₁) * θ hN (a + b₀ + b₁) (cx * c₀ * c₁) /
          (θ hN b₀ c₀ * θ hN (a + b₀) (cx * c₀) * θ hN (a + b₁) (cx * c₁)) := by
  have h := change_of_z2 hN ha1 ha2 hb1 hb2 hb3 hb4 hc0' hcN hx hc0 hc1 hx1 hxz1
  have hθ₀ : θ hN b₀ c₀ ≠ 0 := θ_ne hN (by omega) (by omega) c₀
  have hθx₀ : θ hN (a + b₀) (cx * c₀) ≠ 0 := θ_ne hN (by omega) (by omega) _
  have hD : θ hN b₀ c₀ * θ hN (a + b₀) (cx * c₀) * θ hN (a + b₁) (cx * c₁) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hθ₀ hθx₀) hθ1
  have e : Ab hN hc0' hcN cx c₁ = (Ab hN (a := a) (β := b₀) (by omega) (by omega) cx c₀ *
      θ hN (a + b₀) (cx * c₀) * θ hN b₁ c₁ * θ hN (a + b₁) (cx * c₁) -
      mono b₀ c₀ * hs (kF hN 0) * θ hN (-b₀ + b₁) (c₀⁻¹ * c₁) * θ hN (a + b₀ + b₁) (cx * c₀ * c₁)) /
      (θ hN b₀ c₀ * θ hN (a + b₀) (cx * c₀) * θ hN (a + b₁) (cx * c₁)) := by
    rw [eq_div_iff hD]; linear_combination h
  rw [e]
  field_simp


variable (n : ℕ) (hn : 0 < n)
include hn

lemma spAB_ne_one {a β : ℤ} (hlo : 0 < a + β) (cx cp : ℂ) (ρ s : Fin n) :
    mono (spA (N := N) n a s + spB (N := N) n β ρ s) (spCX n cx * spCP n cp) ≠ 1 := by
  intro h
  have := congrArg (fun f : L => f.coeff 0) h
  have h0 := spAB_lo hN n hn hlo ρ s
  simp [mono, coeff_single_of_ne (show (0 : ℤ) ≠ spA (N := N) n a s + spB (N := N) n β ρ s by omega)] at this

/-- **The `m`-level split**: `A(x,z;q) = θ(z)·Σ_s μ_s A(X_s,Z*_s;Q)/θ(Z*_s;Q) − (theta corrections)`,
`Q = q^{n²}`, for any auxiliary points `Z*_s` admissible for change of `z` against `X_s`. -/
theorem m_split {a β : ℤ} (hlo : 0 < a + β) (hhi : a + β < N) {cx cp : ℂ} (hx : cx ≠ 0) (hp : cp ≠ 0)
    (bz : Fin n → ℤ) (cz : Fin n → ℂ) (hcz : ∀ s, cz s ≠ 0)
    (hA1 : ∀ s : Fin n, -((N * n * n : ℕ) : ℤ) < spA (N := N) n a s)
    (hA2 : ∀ s : Fin n, spA (N := N) n a s < ((N * n * n : ℕ) : ℤ))
    (hb1 : ∀ s : Fin n, 1 ≤ spA (N := N) n a s + bz s)
    (hb2 : ∀ s : Fin n, spA (N := N) n a s + bz s ≤ ((N * n * n : ℕ) : ℤ) - 1)
    (hb3 : ∀ s, 1 ≤ bz s) (hb4 : ∀ s, bz s ≤ ((N * n * n : ℕ) : ℤ) - 1)
    (hx1 : ∀ s : Fin n, mono (spA (N := N) n a s) (spCX n cx) ≠ 1) :
    Aser hN hlo hhi cx cp =
      ∑ s : Fin n, mono (a * (s : ℕ) - N * c2 ((s : ℕ) + 1)) ((-1) ^ ((s : ℕ) : ℤ) * cx ^ ((s : ℕ) : ℤ)) *
          θ hN β cp * (Ab (hN' hN n hn) (a := spA (N := N) n a s) (β := bz s) (by have := hb1 s; omega)
            (by have := hb2 s; omega) (spCX n cx) (cz s) / θ (hN' hN n hn) (bz s) (cz s))
      - ∑ s : Fin n, ∑ ρ : Fin n, mono (spE (N := N) a β ρ s) (spC cx cp ρ s) *
          (mono (bz s) (cz s) * hs (kF (hN' hN n hn) 0) *
            θ (hN' hN n hn) (-bz s + spB (N := N) n β ρ s) ((cz s)⁻¹ * spCP n cp) *
            θ (hN' hN n hn) (spA (N := N) n a s + bz s + spB (N := N) n β ρ s) (spCX n cx * cz s * spCP n cp) /
          (θ (hN' hN n hn) (bz s) (cz s) * θ (hN' hN n hn) (spA (N := N) n a s + bz s) (spCX n cx * cz s) *
            θ (hN' hN n hn) (spA (N := N) n a s + spB (N := N) n β ρ s) (spCX n cx * spCP n cp))) := by
  have hN2 := hN' hN n hn
  have hCX : spCX n cx ≠ 0 := by unfold spCX; simp [hx]
  have hCP : spCP n cp ≠ 0 := by unfold spCP; simp [hp]
  rw [split_A hN n hn hlo hhi hx hp, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hlo' := fun ρ => spAB_lo hN n hn hlo ρ s
  have hhi' := fun ρ => spAB_hi hN n hn hhi ρ s
  have hpiece : ∀ ρ : Fin n, Aser hN2 (hlo' ρ) (hhi' ρ) (spCX n cx) (spCP n cp) =
      θ hN2 (spB (N := N) n β ρ s) (spCP n cp) * Ab hN2 (a := spA (N := N) n a s) (β := bz s)
        (by have := hb1 s; omega) (by have := hb2 s; omega) (spCX n cx) (cz s) / θ hN2 (bz s) (cz s)
      - mono (bz s) (cz s) * hs (kF hN2 0) * θ hN2 (-bz s + spB (N := N) n β ρ s) ((cz s)⁻¹ * spCP n cp) *
          θ hN2 (spA (N := N) n a s + bz s + spB (N := N) n β ρ s) (spCX n cx * cz s * spCP n cp) /
          (θ hN2 (bz s) (cz s) * θ hN2 (spA (N := N) n a s + bz s) (spCX n cx * cz s) *
            θ hN2 (spA (N := N) n a s + spB (N := N) n β ρ s) (spCX n cx * spCP n cp)) := by
    intro ρ
    rw [Aser_eq_Ab hN2 (hlo' ρ) (hhi' ρ) hCX hCP]
    exact coz_solve hN2 (hA1 s) (hA2 s) (hb1 s) (hb2 s) (hb3 s) (hb4 s) _ _ hCX (hcz s) hCP (hx1 s)
      (spAB_ne_one hN n hn hlo cx cp ρ s) (θ_ne hN2 (hlo' ρ) (hhi' ρ) _)
  simp only [hpiece, mul_sub, Finset.sum_sub_distrib]
  congr 1
  rw [← split_coef hN n hn a β hx hp s, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  ring

end MSplit


section Inversion
variable {N : ℕ} (hN : 1 ≤ N)
include hN

lemma aTerm_inv (a β : ℤ) {cx cp : ℂ} (hx : cx ≠ 0) (hp : cp ≠ 0) (r : ℤ)
    (h1 : mono (N * (2 - r - 1) + a + β) (cx * cp) ≠ 1) :
    aTerm N (-a) (-β) cx⁻¹ cp⁻¹ r = -mono (a - β) (cx * cp⁻¹) * aTerm N a β cx cp (2 - r) := by
  unfold aTerm
  set y := mono (N * (2 - r - 1) + a + β) (cx * cp) with hy
  have hy0 : y ≠ 0 := by simp [hy, mono, hx, hp]
  have hyinv : mono (N * (r - 1) + -a + -β) (cx⁻¹ * cp⁻¹) = y⁻¹ := by
    rw [hy, mono, mono, inv_single]; congr 1 <;> [ring; field_simp]
  have h1y : (1 : L) - y ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hm : mono (N * c2 r + -β * r) ((-1) ^ r * cp⁻¹ ^ r) * y =
      mono (a - β) (cx * cp⁻¹) * mono (N * c2 (2 - r) + β * (2 - r)) ((-1) ^ (2 - r) * cp ^ (2 - r)) := by
    rw [hy, mono_mul, mono_mul]
    congr 1
    · have h2 := two_c2 (2 - r); have h3 := two_c2 r; nlinarith
    · have hneg : ((-1 : ℂ)) ^ (2 - r) = (-1) ^ r := by
        rw [show (2 : ℤ) - r = r + 2 * (1 - r) by ring, zpow_add₀ (by norm_num), zpow_mul]; norm_num
      rw [hneg, inv_zpow', zpow_neg, zpow_sub₀ hp]
      field_simp
  rw [hyinv]
  have e : (1 - y⁻¹)⁻¹ = -y * (1 - y)⁻¹ := by
    refine (eq_inv_of_mul_eq_one_right ?_).symm
    field_simp
    ring
  rw [e]
  linear_combination (-(1 - y)⁻¹) * hm

/-- **inversion symmetry** `A(x⁻¹, z⁻¹) = −x z⁻¹ A(x,z)` (equivalently `m(x,q,z) = x⁻¹ m(x⁻¹,q,z⁻¹)`). -/
theorem Ab_inv {a β : ℤ} (hlo : -N < a + β) (hhi : a + β < N) {cx cp : ℂ} (hx : cx ≠ 0) (hp : cp ≠ 0)
    (hxz : mono (a + β) (cx * cp) ≠ 1) :
    Ab hN (a := -a) (β := -β) (by omega) (by omega) cx⁻¹ cp⁻¹ = -mono (a - β) (cx * cp⁻¹) * Ab hN hlo hhi cx cp := by
  rw [Ab_eq_sum, Ab_eq_sum]
  refine hsum_reindex' _ _ (Equiv.subLeft 2) _ fun r => ?_
  simp only [sv, Equiv.subLeft_apply]
  rw [aSumF_apply _ _ _ (inv_ne_zero hx) (inv_ne_zero hp), aSumF_apply _ _ _ hx hp,
    show 2 - r = 2 - r from rfl]
  have h1 : mono (N * (2 - (2 - r) - 1) + a + β) (cx * cp) ≠ 1 := by
    by_cases hr : r = 1
    · subst hr; simpa using hxz
    · intro h
      rw [show (N : ℤ) * (2 - (2 - r) - 1) + a + β = N * (r - 1) + a + β by ring] at h
      have := congrArg (fun f : L => f.coeff 0) h
      have hne : (0 : ℤ) ≠ N * (r - 1) + a + β := by
        have : (N : ℤ) * (r - 1) ≠ -(a + β) := by
          intro h'
          rcases lt_or_gt_of_ne hr with h'' | h''
          · have : (N : ℤ) * (r - 1) ≤ -N := by nlinarith
            omega
          · have : (N : ℤ) ≤ N * (r - 1) := by nlinarith
            omega
        intro h'; apply this; linarith
      simp [mono, coeff_single_of_ne hne] at this
  rw [aTerm_inv hN a β hx hp (2 - r) (by rwa [show 2 - (2 - r) = r by ring] at h1 ⊢), show 2 - (2 - r) = r by ring]

end Inversion

end ALz
