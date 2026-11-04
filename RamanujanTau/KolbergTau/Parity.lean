import RamanujanTau.LehmerSmall.TauModInstances

/-! # `[qⁿ]S₁²(θS₁)² ≡ 0 (mod 4)` for `n ≡ 1 (mod 8)`

Write `S = S₁ = Σσ₁(n)qⁿ` and `T = θS₁ = Σnσ₁(n)qⁿ`. By `sigma_zmod2_support`, `σ₁(m)` is even for
`m ≡ 3,5,6,7 (mod 8)`, and `mσ₁(m)` is even unless `m ≡ 1 (mod 8)`. Hence
`S = a + b + 2c` and `T = d + 2e` with `a = S|_{1 mod 8}`, `b = S|_{0,2,4 mod 8}`, `d = T|_{1 mod 8}`, and
integer series `c, e`. Then `S²T² = (a+b)²d² + 4Z`, and `(a+b)²d² = a²d² + 2abd² + b²d²` is supported on
residues `{4} ∪ {3,5,7} ∪ {0,2,4,6}` mod 8, never on `1`.
-/

set_option autoImplicit false

namespace RamanujanTau.KolbergTau
open RamanujanTau PowerSeries Igusa RamanujanTau.LehmerSmall
open scoped ArithmeticFunction.sigma

/-- Restriction of a series to exponents whose residue mod 8 lies in `s`. -/
noncomputable def res (s : Finset ℕ) (f : PowerSeries ℤ) : PowerSeries ℤ :=
  mk fun n => if n % 8 ∈ s then coeff n f else 0

/-- `f` is supported on exponents with residue mod 8 in `s`. -/
def Supp (s : Finset ℕ) (f : PowerSeries ℤ) : Prop := ∀ n, n % 8 ∉ s → coeff n f = 0

/-- Residue sumset mod 8. -/
def addMod (s t : Finset ℕ) : Finset ℕ := (s ×ˢ t).image fun p => (p.1 + p.2) % 8

lemma supp_res (s : Finset ℕ) (f : PowerSeries ℤ) : Supp s (res s f) := by
  intro n hn; rw [res, coeff_mk, if_neg hn]

lemma supp_mul {s t : Finset ℕ} {f g : PowerSeries ℤ} (hf : Supp s f) (hg : Supp t g) :
    Supp (addMod s t) (f * g) := by
  intro n hn
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.mem_antidiagonal] at hx
  by_cases h1 : x.1 % 8 ∈ s
  · by_cases h2 : x.2 % 8 ∈ t
    · exfalso; apply hn
      rw [addMod, Finset.mem_image]
      exact ⟨(x.1 % 8, x.2 % 8), Finset.mem_product.mpr ⟨h1, h2⟩, by simp only; omega⟩
    · rw [hg _ h2, mul_zero]
  · rw [hf _ h1, zero_mul]

lemma supp_two_mul {s : Finset ℕ} {f : PowerSeries ℤ} (hf : Supp s f) : Supp s (2 * f) := by
  intro n hn
  rw [show (2 : PowerSeries ℤ) = C (2 : ℤ) from (map_ofNat _ _).symm, coeff_C_mul, hf n hn, mul_zero]

lemma supp_add {s : Finset ℕ} {f g : PowerSeries ℤ} (hf : Supp s f) (hg : Supp s g) : Supp s (f + g) := by
  intro n hn; rw [map_add, hf n hn, hg n hn, add_zero]

lemma supp_mono {s t : Finset ℕ} (hst : s ⊆ t) {f : PowerSeries ℤ} (hf : Supp s f) : Supp t f :=
  fun n hn => hf n fun h => hn (hst h)

/-- `σ₁(m)` is even for `m ≡ 3,5,6,7 (mod 8)`. -/
lemma two_dvd_sigma1 {m : ℕ} (hm : m % 8 ∈ ({3, 5, 6, 7} : Finset ℕ)) : (2 : ℤ) ∣ (σ 1 m : ℤ) := by
  have h : (σ 1 m : ZMod 2) = 0 := by
    by_contra hc
    have := sigma_zmod2_support 1 hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    omega
  have : ((σ 1 m : ℤ) : ZMod 2) = 0 := by exact_mod_cast h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp this

/-- `mσ₁(m)` is even for `m ≢ 1 (mod 8)`. -/
lemma two_dvd_theta_sigma1 {m : ℕ} (hm : m % 8 ∉ ({1} : Finset ℕ)) :
    (2 : ℤ) ∣ (m : ℤ) * (σ 1 m : ℤ) := by
  simp only [Finset.mem_singleton] at hm
  rcases Nat.even_or_odd m with ⟨r, hr⟩ | hodd
  · exact Dvd.dvd.mul_right ⟨(r : ℤ), by rw [hr]; push_cast; ring⟩ _
  · rw [Nat.odd_iff] at hodd
    exact Dvd.dvd.mul_left (two_dvd_sigma1 (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)) _

noncomputable def sS : PowerSeries ℤ := Sk 1
noncomputable def sT : PowerSeries ℤ := theta (Sk 1)

noncomputable def pa : PowerSeries ℤ := res {1} sS
noncomputable def pb : PowerSeries ℤ := res {0, 2, 4} sS
noncomputable def pc : PowerSeries ℤ :=
  mk fun n => if n % 8 ∈ ({3, 5, 6, 7} : Finset ℕ) then coeff n sS / 2 else 0
noncomputable def pd : PowerSeries ℤ := res {1} sT
noncomputable def pe : PowerSeries ℤ := mk fun n => if n % 8 ∈ ({1} : Finset ℕ) then 0 else coeff n sT / 2

lemma coeff_sS (n : ℕ) : coeff n sS = (σ 1 n : ℤ) := by rw [sS, Sk, coeff_mk]
lemma coeff_sT (n : ℕ) : coeff n sT = (n : ℤ) * (σ 1 n : ℤ) := by rw [sT, coeff_theta, Sk, coeff_mk]

lemma S_decomp : sS = pa + pb + 2 * pc := by
  ext n
  rw [show (2 : PowerSeries ℤ) = C (2 : ℤ) from (map_ofNat _ _).symm]
  simp only [map_add, coeff_C_mul, pa, pb, pc, res, coeff_mk]
  have h8 : n % 8 < 8 := Nat.mod_lt _ (by norm_num)
  by_cases h1 : n % 8 ∈ ({3, 5, 6, 7} : Finset ℕ)
  · have h2 := two_dvd_sigma1 h1
    rw [coeff_sS] at *
    have ha : n % 8 ∉ ({1} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1 ⊢; omega
    have hb : n % 8 ∉ ({0, 2, 4} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1 ⊢; omega
    rw [if_neg ha, if_neg hb, if_pos h1, Int.mul_ediv_cancel' h2]; ring
  · rw [if_neg h1, coeff_sS]
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 ⊢
    by_cases ha : n % 8 = 1
    · rw [if_pos ha, if_neg (by omega)]; ring
    · rw [if_neg ha, if_pos (by omega)]; ring

lemma T_decomp : sT = pd + 2 * pe := by
  ext n
  rw [show (2 : PowerSeries ℤ) = C (2 : ℤ) from (map_ofNat _ _).symm]
  simp only [map_add, coeff_C_mul, pd, pe, res, coeff_mk]
  by_cases h1 : n % 8 ∈ ({1} : Finset ℕ)
  · rw [if_pos h1, if_pos h1]; ring
  · rw [if_neg h1, if_neg h1, coeff_sT, Int.mul_ediv_cancel' (two_dvd_theta_sigma1 h1)]; ring

/-- **Milestone K1.** `[qⁿ]S₁²(θS₁)² ≡ 0 (mod 4)` for `n ≡ 1 (mod 8)`. -/
theorem coeff_A_mod4 {n : ℕ} (hn : n % 8 = 1) :
    (4 : ℤ) ∣ coeff n (Sk 1 ^ 2 * theta (Sk 1) ^ 2) := by
  have hA : Sk 1 ^ 2 * theta (Sk 1) ^ 2 =
      pa * pa * (pd * pd) + 2 * (pa * pb * (pd * pd)) + pb * pb * (pd * pd) +
        4 * ((pa + pb) ^ 2 * pe * (pd + pe) + pc * (pa + pb + pc) * (pd + 2 * pe) ^ 2) := by
    rw [show theta (Sk 1) = sT from rfl, show Sk 1 = sS from rfl, S_decomp, T_decomp]; ring
  have ha : Supp {1} pa := supp_res _ _
  have hb : Supp {0, 2, 4} pb := supp_res _ _
  have hd : Supp {1} pd := supp_res _ _
  have hdd := supp_mul hd hd
  have h1 := supp_mul (supp_mul ha ha) hdd
  have h2 := supp_two_mul (supp_mul (supp_mul ha hb) hdd)
  have h3 := supp_mul (supp_mul hb hb) hdd
  have hn1 : ∀ s : Finset ℕ, 1 ∉ s → n % 8 ∉ s := fun s hs => by rwa [hn]
  rw [hA, map_add, map_add, map_add, h1 n (hn1 _ (by decide)), h2 n (hn1 _ (by decide)),
    h3 n (hn1 _ (by decide)), show (4 : PowerSeries ℤ) = C (4 : ℤ) from (map_ofNat _ _).symm,
    coeff_C_mul]
  simp

end RamanujanTau.KolbergTau

#print axioms RamanujanTau.KolbergTau.coeff_A_mod4
