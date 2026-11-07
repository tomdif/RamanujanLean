import RamanujanTau.BLBound.Integral
import RamanujanTau.TheoremA.BWDictionary

/-!
# The image of `D̄` (Lemma 2)

For `ℓ ≥ 13`, `D̄` maps the reductions of weight `ℓ-1` forms into `Δ^t S_{k'}`, where `t = ⌊ℓ/24⌋` and
`k' = (ℓ+j-2)/2`.
-/

set_option autoImplicit false

namespace RamanujanTau.BLBound
open ModularForm UpperHalfPlane ModP BoylanWebb
open RamanujanTau.TheoremA.HalfIntegral RamanujanTau.TheoremA.SignLattice
open RankProof (Ea)
open scoped MatrixGroups
open RamanujanTau.Mod691 (p4 p6)

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- The weight class of the image. -/
lemma image_weight (h13 : 13 ≤ ℓ) {w : ℕ}
    (hmod : w % (ℓ - 1) = (12 * rho ℓ + (ℓ - 1)) % (ℓ - 1))
    (hle : ℓ * w ≤ (12 * rho ℓ + (ℓ - 1)) + (ℓ - 1) * (ℓ + 1)) :
    ∃ n : ℕ, (ℓ + jj ℓ - 2) / 2 = w + n * (ℓ - 1) := by
  have hρ := h24rho h13
  have hd := ell_decomp (ℓ := ℓ)
  have hj := ell_mod h13
  obtain ⟨i, hi⟩ : ∃ i, jj ℓ = 2 * i + 1 := ⟨jj ℓ / 2, by omega⟩
  obtain ⟨L, hL⟩ : ∃ L, ℓ = L + 1 := ⟨ℓ - 1, by omega⟩
  set t := tt ℓ with htdef
  set ρ := rho ℓ with hρdef
  set K := (ℓ + jj ℓ - 2) / 2 with hK
  have hKe : K = 12 * t + 2 * i := by omega
  have hti : 3 ≤ 12 * t + i := by omega
  have hL1 : ℓ - 1 = L := by omega
  rw [hL1] at hmod hle
  have hLpos : 12 ≤ L := by omega
  have h12 : 12 * ρ = K + i * L := by
    have h1 : 24 * ρ + 1 = (2 * i + 1) * (L + 1) := by
      rw [← hi, ← hL]
      exact hρ
    have h2 : 2 * K + 1 = L + 1 + 2 * i := by omega
    nlinarith
  have hK0 : (12 * ρ + L) % L = K % L := by
    rw [h12, show K + i * L + L = K + L * (i + 1) by ring, Nat.add_mul_mod_self_left]
  have hmod2 : w % L = K % L := hmod.trans hK0
  have hwK : w ≤ K := by
    by_contra hc
    have hgt : K < w := not_le.mp hc
    obtain ⟨m, hm⟩ := (Nat.modEq_iff_exists_eq_add hgt.le).mp hmod2.symm
    have hm0 : 1 ≤ m := by
      by_contra h0
      have : m = 0 := by omega
      subst this
      omega
    have hw2 : K + L ≤ w := by nlinarith
    have h3 : ℓ * (K + L) ≤ ℓ * w := Nat.mul_le_mul_left _ hw2
    rw [h12, hL] at hle
    rw [hL] at h3
    have h4 : (L + 1) * (K + L) ≤ K + i * L + L + L * (L + 1 + 1) := h3.trans hle
    have h5 : L * (K + L) ≤ L * (i + 1 + L + 1 + 1 - 1 - 1 + 0) := by
      have e : i + 1 + L + 1 + 1 - 1 - 1 + 0 = i + L + 1 := by omega
      rw [e]
      nlinarith
    have h6 := Nat.le_of_mul_le_mul_left h5 (by omega)
    omega
  obtain ⟨m, hm⟩ := (Nat.modEq_iff_exists_eq_add hwK).mp hmod2
  exact ⟨m, by rw [hL1, hm]; ring⟩

/-- The target weight is even and at least four. -/
lemma kprime_form (h13 : 13 ≤ ℓ) : 4 ≤ (ℓ + jj ℓ - 2) / 2 ∧ Even ((ℓ + jj ℓ - 2) / 2) := by
  have hd := ell_decomp (ℓ := ℓ)
  have hj := ell_mod h13
  constructor
  · omega
  · rw [Nat.even_iff]
    omega

/-- A form in the lattice from a reduction with constant term zero. -/
theorem exists_lattice (h13 : 13 ≤ ℓ) {h : PowerSeries (ZMod ℓ)}
    (hF : FormBar ℓ ((ℓ + jj ℓ - 2) / 2) h) (h0 : PowerSeries.coeff 0 h = 0) :
    ∃ a ∈ intLattice ℓ, Ψ ℓ a = h := by
  obtain ⟨P, hP, rfl⟩ := hF
  obtain ⟨c, hc, hcΨ⟩ := lift_iso ℓ _ P hP
  obtain ⟨hk4, hkev⟩ := kprime_form (ℓ := ℓ) h13
  set k := (ℓ + jj ℓ - 2) / 2 with hk
  have hn' : 4 * bexp0 k + 6 * bexp1 k = k := by
    obtain ⟨m, hm⟩ := hkev
    unfold bexp0 bexp1
    omega
  set m := p4 ^ bexp0 k * p6 ^ bexp1 k with hm
  have hmF : IntForm (k : ℤ) m := (IntForm.mono _ _).cast (by rw [hn'])
  have hm0 : PowerSeries.constantCoeff m = 1 := by
    rw [hm, map_mul, map_pow, map_pow]
    have h4 : PowerSeries.constantCoeff p4 = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, RamanujanTau.Mod691.coeff_p4]; simp
    have h6 : PowerSeries.constantCoeff p6 = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, RamanujanTau.Mod691.coeff_p6]; simp
    rw [h4, h6, one_pow, one_pow, one_mul]
  have hc0 : ((PowerSeries.coeff 0 c : ℤ) : ZMod ℓ) = 0 := by
    have e : PowerSeries.coeff 0 (Ψ ℓ c) = 0 := by rw [hcΨ]; exact h0
    rwa [PowerSeries.coeff_map] at e
  set a := c - PowerSeries.C (PowerSeries.coeff 0 c) * m with ha
  have haF : IntForm (k : ℤ) a := hc.sub (hmF.C_mul _)
  have ha0 : PowerSeries.coeff 0 a = 0 := by
    rw [ha, map_sub, PowerSeries.coeff_zero_eq_constantCoeff_apply (PowerSeries.C _ * m), map_mul,
      PowerSeries.constantCoeff_C, hm0, mul_one, sub_self]
  have hΨa : Ψ ℓ a = ev (ZMod ℓ) P := by
    have hz : (Int.castRingHom (ZMod ℓ)) (PowerSeries.coeff 0 c) = 0 := hc0
    rw [ha, map_sub, map_mul, PowerSeries.map_C, hcΨ, hz, map_zero, zero_mul, sub_zero]
  refine ⟨a, ?_, hΨa⟩
  obtain ⟨F, hFa⟩ := haF
  have hF0 : (qExpansion 1 F).coeff 0 = 0 := by rw [hFa, PowerSeries.coeff_map, ha0, map_zero]
  exact ⟨ModularForm.toCuspForm F hF0, hFa.symm⟩

/-- **Lemma 2: the image of `D̄`.** -/
theorem D_image (h13 : 13 ≤ ℓ) {f : PowerSeries (ZMod ℓ)} (hf : FormBar ℓ (ℓ - 1) f) :
    ∃ a ∈ intLattice ℓ, U ℓ (Ψ ℓ (Φ ℓ) * f) = Ψ ℓ (Dz ^ tt ℓ * a) := by
  have h5 : 5 ≤ ℓ := by omega
  have hp := hℓ.out
  obtain ⟨P, hP, rfl⟩ := hf
  obtain ⟨b, hb, hbΨ⟩ := lift_iso ℓ _ P hP
  have hρ := h24rho h13
  have hρpos : 1 ≤ rho ℓ := by
    by_contra h0
    have h00 : rho ℓ = 0 := by omega
    rw [h00] at hρ
    have hj := ell_mod h13
    have : jj ℓ * ℓ ≥ 13 := by nlinarith [show 1 ≤ jj ℓ by omega]
    omega
  set g := Dz ^ rho ℓ * b with hg
  have hgF : IntForm ((12 * rho ℓ + (ℓ - 1) : ℕ) : ℤ) g :=
    ((IntForm.disc.pow (rho ℓ)).mul hb).cast (by push_cast; ring)
  have hg0 : PowerSeries.coeff 0 g = 0 := by
    rw [hg, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_pow]
    simp [Dz, Nat.ne_of_gt hρpos]
  set K := 12 * rho ℓ + (ℓ - 1) with hK
  have hKpos : 1 ≤ K - 1 := by omega
  have hbarg : FormBar ℓ K (Ψ ℓ g) := formBar_of_intForm ℓ h5 (K + 1) K (by omega) g hgF
  have hT := hgF.hecke ℓ (K - 1) (by push_cast [Nat.cast_sub (show 1 ≤ K by omega)]; ring) hg0
  have hbarU : FormBar ℓ K (U ℓ (Ψ ℓ g)) := by
    have := formBar_of_intForm ℓ h5 (K + 1) K (by omega) _ hT
    rwa [Ψ_hecke ℓ (K - 1) hKpos] at this
  obtain ⟨w, hw1, hw2, hw3⟩ := U_filtration h5 hbarg hbarU
  obtain ⟨n, hn⟩ := image_weight h13 hw1 hw2
  have hbark : FormBar ℓ ((ℓ + jj ℓ - 2) / 2) (U ℓ (Ψ ℓ g)) := by
    rw [hn]
    exact hw3.up h5 n
  have hc0 : PowerSeries.coeff 0 (U ℓ (Ψ ℓ g)) = 0 := by
    rw [coeff_U, mul_zero, PowerSeries.coeff_map, hg0, map_zero]
  obtain ⟨a, ha, haΨ⟩ := exists_lattice h13 hbark hc0
  refine ⟨a, ha, ?_⟩
  have hδ : Ψ ℓ (Φ ℓ) = Ψ ℓ (Ea ℓ (hℓ0 ℓ) (Dz ^ tt ℓ)) * Ψ ℓ (Dz ^ rho ℓ) := by
    rw [Ψ_Φ ℓ (h24 h13), delta_eq h13, pow_add, map_mul, frob_Dz]
  have hstep : U ℓ (Ψ ℓ (Φ ℓ) * ev (ZMod ℓ) P) = Ψ ℓ (U ℓ (Ea ℓ (hℓ0 ℓ) (Dz ^ tt ℓ) * g)) := by
    rw [map_U, map_mul, hδ, hg, map_mul, hbΨ, mul_assoc]
  rw [hstep, U_Ea_mul, map_mul, map_mul, map_U, haΨ]

end RamanujanTau.BLBound
