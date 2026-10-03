/-
# Base splitting of Appell–Lerch sums: `q → q^{n²}`

`A(x,z;q) = Σ_{ρ<n} Σ_{s<n} [prefactor] · A(X_{ρ,s}, Z_{ρ,s}; q^{n²})` by splitting
`r = n m − ρ`, `j = n j' + s` in the cone expansion. The new arguments involve `x, z` only through
`xⁿ, zⁿ` (so roots of unity drop out of the arguments).
-/
import RamanujanTau.ALJacobi

set_option autoImplicit false

namespace ALz
open HahnSeries Finset

section SplitEquiv
variable (n : ℕ) (hn : 0 < n)
include hn

/-- `(r, j) ↦ ((ρ, s), (m, j'))` with `r = n m − ρ`, `j = n j' + s`, `0 ≤ ρ, s < n`. -/
def splitEquiv : ℤ × ℤ ≃ (Fin n × Fin n) × (ℤ × ℤ) where
  toFun p := ((⟨((-p.1) % n).toNat, by
      have h1 := Int.emod_nonneg (-p.1) (show (n : ℤ) ≠ 0 by omega)
      have h2 := Int.emod_lt_of_pos (-p.1) (show (0 : ℤ) < n by omega)
      omega⟩,
    ⟨(p.2 % n).toNat, by
      have h1 := Int.emod_nonneg p.2 (show (n : ℤ) ≠ 0 by omega)
      have h2 := Int.emod_lt_of_pos p.2 (show (0 : ℤ) < n by omega)
      omega⟩), ((p.1 + (-p.1) % n) / n, p.2 / n))
  invFun q := (n * q.2.1 - (q.1.1 : ℕ), n * q.2.2 + (q.1.2 : ℕ))
  left_inv p := by
    obtain ⟨r, j⟩ := p
    have hn' : (n : ℤ) ≠ 0 := by omega
    have h1 := Int.emod_nonneg (-r) hn'
    have h2 := Int.emod_nonneg j hn'
    have hd : (n : ℤ) ∣ r + (-r) % n := by
      have := Int.emod_emod_of_dvd (-r) (dvd_refl (n : ℤ))
      rw [Int.dvd_iff_emod_eq_zero, Int.add_emod, Int.emod_emod_of_dvd _ (dvd_refl _),
        ← Int.add_emod, add_neg_cancel, Int.zero_emod]
    simp only [Prod.mk.injEq]
    constructor
    · rw [Int.mul_ediv_cancel' hd, Int.toNat_of_nonneg h1]; ring
    · rw [Int.toNat_of_nonneg h2]; exact Int.mul_ediv_add_emod j n
  right_inv q := by
    obtain ⟨⟨ρ, s⟩, ⟨m, J⟩⟩ := q
    have hn' : (n : ℤ) ≠ 0 := by omega
    have hρ : ((ρ : ℕ) : ℤ) < n := by exact_mod_cast ρ.2
    have hs : ((s : ℕ) : ℤ) < n := by exact_mod_cast s.2
    have e1 : (-(n * m - (ρ : ℕ) : ℤ)) % n = (ρ : ℕ) := by
      rw [show -(n * m - ((ρ : ℕ) : ℤ)) = (ρ : ℕ) + n * (-m) by ring, Int.add_mul_emod_self_left,
        Int.emod_eq_of_lt (by positivity) hρ]
    have e2 : (n * J + (s : ℕ) : ℤ) % n = (s : ℕ) := by
      rw [show (n : ℤ) * J + (s : ℕ) = (s : ℕ) + n * J by ring, Int.add_mul_emod_self_left,
        Int.emod_eq_of_lt (by positivity) hs]
    simp only [Prod.mk.injEq, e1, e2, Int.toNat_natCast]
    refine ⟨trivial, ?_, ?_⟩
    · rw [show (n : ℤ) * m - (ρ : ℕ) + (ρ : ℕ) = n * m by ring, Int.mul_ediv_cancel_left _ hn']
    · rw [show (n : ℤ) * J + (s : ℕ) = (s : ℕ) + n * J by ring, Int.add_mul_ediv_left _ _ hn',
        Int.ediv_eq_zero_of_lt (by positivity) hs, zero_add]

end SplitEquiv


section Split
variable {N : ℕ} (hN : 1 ≤ N) (n : ℕ) (hn : 0 < n)

/-- prefactor exponent `E(r = −ρ, j = s)`. -/
def spE (a β : ℤ) (ρ s : ℕ) : ℤ :=
  N * c2 (-(ρ : ℤ)) + N * (s : ℤ) * (-(ρ : ℤ) - 1) + a * s + β * ((s : ℤ) - ρ)
/-- prefactor coefficient. -/
noncomputable def spC (cx cp : ℂ) (ρ s : ℕ) : ℂ := (-1) ^ (-(ρ : ℤ)) * cp ^ (-(ρ : ℤ)) * (cx * cp) ^ (s : ℤ)
/-- new `x`-exponent. -/
def spA (a : ℤ) (s : ℕ) : ℤ := N * c2 n - N * n * s + a * n
/-- new `z`-exponent. -/
def spB (β : ℤ) (ρ s : ℕ) : ℤ := N * c2 n - N * n * ρ + N * n * s + β * n
/-- new `z`-constant `(−1)^{n+1} c_pⁿ`. -/
noncomputable def spCP (cp : ℂ) : ℂ := (-1) ^ (n + 1) * cp ^ n
/-- new `x`-constant `(−1)^{n+1} c_xⁿ`. -/
noncomputable def spCX (cx : ℂ) : ℂ := (-1) ^ (n + 1) * cx ^ n

include hN hn

lemma hN' : 1 ≤ N * n * n := Nat.one_le_iff_ne_zero.mpr (by positivity)

lemma spAB_lo {a β : ℤ} (hlo : 0 < a + β) (ρ s : Fin n) :
    0 < spA (N := N) n a s + spB (N := N) n β ρ s := by
  unfold spA spB
  have h := two_c2 (n : ℤ)
  have hρ : ((ρ : ℕ) : ℤ) < n := by exact_mod_cast ρ.2
  have : (0 : ℤ) ≤ N * (n - 1 - ρ) * n := mul_nonneg (mul_nonneg (by positivity) (by omega)) (by positivity)
  nlinarith

lemma spAB_hi {a β : ℤ} (hhi : a + β < N) (ρ s : Fin n) :
    spA (N := N) n a s + spB (N := N) n β ρ s < (N * n * n : ℕ) := by
  unfold spA spB
  have h := two_c2 (n : ℤ)
  have : (0 : ℤ) ≤ N * ρ * n := by positivity
  push_cast
  have : (a + β) * n < N * n := mul_lt_mul_of_pos_right hhi (by exact_mod_cast hn)
  nlinarith


omit hN in
lemma cone_split {m J ρ s : ℤ} (h0 : 0 ≤ ρ) (h1 : ρ < n) (h2 : 0 ≤ s) (h3 : s < n) :
    cone (n * m - ρ) (n * J + s) ↔ cone m J := by
  have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have a1 : 1 ≤ n * m - ρ ↔ 1 ≤ m := by
    constructor
    · intro h; by_contra hm; push Not at hm; nlinarith
    · intro h; nlinarith
  have a2 : 0 ≤ n * J + s ↔ 0 ≤ J := by
    constructor
    · intro h; by_contra hm; push Not at hm; nlinarith
    · intro h; nlinarith
  unfold cone
  constructor
  · rintro (⟨h, h'⟩ | ⟨h, h'⟩)
    · exact Or.inl ⟨a1.mp h, a2.mp h'⟩
    · right; constructor
      · by_contra hm; push Not at hm; exact absurd (a1.mpr (by omega)) (by omega)
      · by_contra hm; push Not at hm; exact absurd (a2.mpr (by omega)) (by omega)
  · rintro (⟨h, h'⟩ | ⟨h, h'⟩)
    · exact Or.inl ⟨a1.mpr h, a2.mpr h'⟩
    · right; constructor
      · by_contra hm; push Not at hm; exact absurd (a1.mp hm) (by omega)
      · by_contra hm; push Not at hm; exact absurd (a2.mp hm) (by omega)

omit hN in
lemma sgnC_split {m ρ : ℤ} (h0 : 0 ≤ ρ) (h1 : ρ < n) : sgnC (n * m - ρ) = sgnC m := by
  have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
  unfold sgnC
  by_cases hm : 1 ≤ m
  · rw [if_pos hm, if_pos (by nlinarith)]
  · rw [if_neg hm, if_neg (by push Not at hm ⊢; nlinarith)]

lemma split_pt {a β : ℤ} (hlo : 0 < a + β) (hhi : a + β < N) {cx cp : ℂ} (hx : cx ≠ 0) (hp : cp ≠ 0)
    (ρ s : Fin n) (m J : ℤ) :
    asF hN hlo hhi cx cp (n * m - (ρ : ℕ), n * J + (s : ℕ)) =
      mono (spE (N := N) a β ρ s) (spC cx cp ρ s) *
        asF (hN' hN n hn) (spAB_lo hN n hn hlo ρ s) (spAB_hi hN n hn hhi ρ s) (spCX n cx) (spCP n cp) (m, J) := by
  have hρ0 : (0 : ℤ) ≤ (ρ : ℕ) := by positivity
  have hρ1 : ((ρ : ℕ) : ℤ) < n := by exact_mod_cast ρ.2
  have hs0 : (0 : ℤ) ≤ (s : ℕ) := by positivity
  have hs1 : ((s : ℕ) : ℤ) < n := by exact_mod_cast s.2
  rw [asF_apply, asF_apply]
  simp only
  have hcs := cone_split n hn (m := m) (J := J) hρ0 hρ1 hs0 hs1
  by_cases hc : cone m J
  · rw [if_pos (hcs.mpr hc), if_pos hc, mono_mul, sgnC_split n hn hρ0 hρ1]
    congr 1
    · unfold asExp spE spA spB
      have h0 := two_c2 ((n : ℤ) * m - (ρ : ℕ)); have h1 := two_c2 (n : ℤ)
      have h2 := two_c2 (-((ρ : ℕ) : ℤ)); have h3 := two_c2 m
      have : (2 : ℤ) * ((N : ℤ) * c2 (n * m - (ρ : ℕ)) + β * (n * m - (ρ : ℕ)) +
          (N * (n * m - (ρ : ℕ) - 1) + a + β) * (n * J + (s : ℕ))) =
        2 * ((N : ℤ) * c2 (-((ρ : ℕ) : ℤ)) + N * ((s : ℕ) : ℤ) * (-((ρ : ℕ) : ℤ) - 1) + a * (s : ℕ) +
          β * ((s : ℕ) - (ρ : ℕ)) + (((N * n * n : ℕ) : ℤ) * c2 m +
          (N * c2 n - N * n * (ρ : ℕ) + N * n * (s : ℕ) + β * n) * m +
          (((N * n * n : ℕ) : ℤ) * (m - 1) + (N * c2 n - N * n * (s : ℕ) + a * n) +
            (N * c2 n - N * n * (ρ : ℕ) + N * n * (s : ℕ) + β * n)) * J)) := by
        push_cast
        linear_combination (N : ℤ) * h0 - (N : ℤ) * (2 * J + m) * h1 - (N : ℤ) * h2 - (N : ℤ) * n ^ 2 * h3
      omega
    · unfold spC spCX spCP
      have hm1 : ((-1 : ℂ)) ≠ 0 := by norm_num
      set ρz : ℤ := ((ρ : ℕ) : ℤ)
      set sz : ℤ := ((s : ℕ) : ℤ)
      have hL : sgnC m * (-1) ^ ((n : ℤ) * m - ρz) * cp ^ ((n : ℤ) * m - ρz) * (cx * cp) ^ ((n : ℤ) * J + sz) =
          sgnC m * ((-1) ^ (-ρz) * cp ^ (-ρz) * (cx * cp) ^ sz) * (((-1) ^ n * cp ^ n) ^ m * ((cx * cp) ^ n) ^ J) := by
        rw [show (n : ℤ) * m - ρz = n * m + -ρz by ring, zpow_add₀ hm1, zpow_add₀ hp,
          zpow_add₀ (mul_ne_zero hx hp), zpow_mul, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast,
          zpow_natCast, mul_zpow ((-1 : ℂ) ^ n)]
        ring
      have hR1 : ((-1 : ℂ)) ^ m * ((-1) ^ (n + 1) * cp ^ n) ^ m = ((-1) ^ n * cp ^ n) ^ m := by
        rw [← mul_zpow]; congr 1; ring
      have hR2 : ((-1 : ℂ) ^ (n + 1) * cx ^ n * ((-1) ^ (n + 1) * cp ^ n)) = (cx * cp) ^ n := by
        have : ((-1 : ℂ) ^ (n + 1)) * (-1) ^ (n + 1) = 1 := by rw [← mul_pow]; norm_num
        rw [mul_pow]; linear_combination (cx ^ n * cp ^ n) * this
      rw [hL, hR2, ← hR1]; ring
  · rw [if_neg (fun h => hc (hcs.mp h)), if_neg hc, mul_zero]


omit hN hn in
lemma hs_fintype {ι : Type*} [Fintype ι] (S : SummableFamily ℤ ℂ ι) : hs S = ∑ i, S i := by
  ext k
  rw [hs, SummableFamily.coeff_hsum, finsum_eq_sum_of_fintype, HahnSeries.coeff_sum]

/-- **Base splitting**: `A(x,z;q) = Σ_{ρ,s<n} q^{…}·(…) · A(X_{ρ,s}, Z_{ρ,s}; q^{n²})`. -/
theorem split_A {a β : ℤ} (hlo : 0 < a + β) (hhi : a + β < N) {cx cp : ℂ} (hx : cx ≠ 0) (hp : cp ≠ 0) :
    Aser hN hlo hhi cx cp = ∑ ρ : Fin n, ∑ s : Fin n, mono (spE (N := N) a β ρ s) (spC cx cp ρ s) *
      Aser (hN' hN n hn) (spAB_lo hN n hn hlo ρ s) (spAB_hi hN n hn hhi ρ s) (spCX n cx) (spCP n cp) := by
  set S := SummableFamily.Equiv (splitEquiv n hn) (asF hN hlo hhi cx cp)
  have h1 : Aser hN hlo hhi cx cp = hs (rowFam S) := by
    rw [hs_rowFam, hs_eq, SummableFamily.hsum_equiv]; rfl
  rw [h1, hs_fintype, ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun s _ => ?_
  rw [rowFam_apply]
  refine hsum_reindex _ _ (Equiv.refl _) _ fun ⟨m, J⟩ => ?_
  simp only [Equiv.refl_apply, row_apply, S, SummableFamily.Equiv_toFun]
  exact split_pt hN n hn hlo hhi hx hp ρ s m J

end Split

end ALz
