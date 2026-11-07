import RamanujanTau.OnoWeaverMore.Core
import RamanujanTau.OnoWeaverMore.EigenLiftJ
import RamanujanTau.OnoWeaverMore.DimOneData2931
import RamanujanTau.FiniteArithmetic.Cert29
import RamanujanTau.FiniteArithmetic.Cert31

/-!
# The eigen-relation `T(Q²) G ≡ ν G (mod ℓ)` at ℓ = 29 and 31, for every prime `Q ≥ 5`

Here `S_{ℓ−1}` is two-dimensional, but the relevant half-integral space is not:
`η^{−ℓ} S_{ℓ−1} ⊃ η^{−j} S_{k'}` with `j = ℓ − 24`, `k' = (ℓ+j−2)/2 = 16, 18`, and
`S_{16} = ℂ·ΔE₄`, `S_{18} = ℂ·ΔE₆` are one-dimensional. The mod-ℓ seeds
`Cert29.seed : U₂₉(Δ³⁵) ≡ 8·Δ²E₄` and `Cert31.seed : U₃₁(Δ⁴⁰) ≡ 10·Δ²E₆` show that
`G = Σ p(ℓN − δ) q^N ≡ c·Δ²E·P^ℓ = c·X·(ΔE·P^j)` lies in the reduction of that line
(`Δ·P²⁴ = X`). On `coordOf ℓ (ΔE)` the operator `T(Q²)` (index `j`) is an exact eigen-operator
in characteristic zero (`EigenLiftJ.eigen_char0J` with `DimOne40.dimOne_29/31`; the normalized
coefficient `a(1) = 1`), and multiplication by `X` intertwines the operator in index `j` with
the one in index `j + 24 = ℓ` (`heckeHalf_X_mul`). Hence `T(Q²)G ≡ ν G (mod ℓ)` for some `ν`
(`eigen_29`, `eigen_31`). No `EtaHecke`-type hypothesis is involved.
-/

set_option autoImplicit false

namespace RamanujanTau.OnoWeaverMore
open PowerSeries BoylanWebb RamanujanTau.AtkinSporadic
open RamanujanTau.TheoremA RamanujanTau.TheoremA.HalfIntegral RamanujanTau.TheoremA.SignLattice
open MockTheta5.JTP (qfacInf partitionGF)
open Weaver (wlam)

lemma coeff_X_mul' {R : Type*} [CommRing R] (c : PowerSeries R) (k : ℕ) :
    coeff k (X * c) = if k = 0 then 0 else coeff (k - 1) c := by
  rcases k with _ | k
  · simp
  · rw [coeff_succ_X_mul]; simp

/-- **Shifting the index by 24.** Multiplication by `X` intertwines `T(Q²)` on `η^{−j}` and
on `η^{−(j+24)}` coordinates. -/
lemma heckeHalf_X_mul {R : Type*} [CommRing R] (Q : ℕ) [hQ : Fact Q.Prime] (hQ5 : 5 ≤ Q)
    (j j' lam : ℕ) (s : ℤ) (hj : j' = j + 24) (hj24 : j < 24) (c : PowerSeries R)
    (hc0 : coeff 0 c = 0) :
    heckeHalf Q j' lam s (X * c) = X * heckeHalf Q j lam s c := by
  obtain ⟨hQ2, hQ3⟩ := Equivariance.prime_ge_five hQ.out hQ5
  have hd := Equivariance.hshift_spec hQ2 hQ3 j
  have hd' := Equivariance.hshift_spec hQ2 hQ3 j'
  have hQ25 : 25 ≤ Q ^ 2 := by nlinarith
  set d := hshift Q j with hddef
  set d' := hshift Q j' with hd'def
  have hdd : d' = d + (Q ^ 2 - 1) := by
    rw [hj, mul_add] at hd'
    omega
  have hdle : d ≤ Q ^ 2 - 1 := by
    have : (Q ^ 2 - 1) * j ≤ (Q ^ 2 - 1) * 24 := Nat.mul_le_mul_left _ hj24.le
    omega
  have hQpos : 0 < Q ^ 2 := by omega
  ext N
  rcases N with _ | n
  · -- coefficient `0`: every term vanishes
    simp only [coeff_heckeHalf, coeff_zero_X_mul, ← hd'def]
    rw [if_neg (by omega), mul_zero, zero_add, zero_add]
    split_ifs with h3
    · have hq : (0 + d') / Q ^ 2 = 1 := by
        rw [zero_add, hdd]
        have h1 : d + (Q ^ 2 - 1) = (d - 1) + Q ^ 2 := by
          obtain ⟨k, hk⟩ := h3
          rw [zero_add, hdd] at hk
          have : 1 ≤ d := by
            by_contra h0
            have hd0 : d = 0 := by omega
            rw [hd0, zero_add] at hk
            rcases k with _ | k
            · omega
            · have : Q ^ 2 ≤ Q ^ 2 * (k + 1) := Nat.le_mul_of_pos_right _ (by omega)
              omega
          omega
        rw [h1, Nat.add_div_right _ hQpos, Nat.div_eq_of_lt (by omega)]
      rw [hq, coeff_X_mul', if_neg one_ne_zero, Nat.sub_self, hc0, mul_zero]
    · rfl
  · have hleg : (24 * ((n + 1 : ℕ) : ℤ) - (j' : ℤ)) = 24 * (n : ℤ) - j := by
      rw [hj]; push_cast; ring
    simp only [coeff_succ_X_mul, coeff_heckeHalf, ← hddef, ← hd'def, hleg]
    congr 1
    · congr 1
      by_cases h1 : d ≤ Q ^ 2 * n
      · have e : Q ^ 2 * (n + 1) - d' = (Q ^ 2 * n - d) + 1 := by
          rw [hdd, Nat.mul_succ]; omega
        rw [if_pos (by rw [hdd, Nat.mul_succ]; omega), if_pos h1, e, coeff_X_mul',
          if_neg (Nat.succ_ne_zero _), Nat.add_sub_cancel]
      · rw [if_neg h1]
        split_ifs with h2
        · have e : Q ^ 2 * (n + 1) - d' = 0 := by rw [hdd, Nat.mul_succ] at h2 ⊢; omega
          rw [e, coeff_zero_X_mul]
        · rfl
    · have hdv : Q ^ 2 ∣ n + 1 + d' ↔ Q ^ 2 ∣ n + d := by
        rw [hdd, show n + 1 + (d + (Q ^ 2 - 1)) = n + d + Q ^ 2 by omega]
        exact Nat.dvd_add_self_right
      by_cases h3 : Q ^ 2 ∣ n + d
      · rw [if_pos (hdv.mpr h3), if_pos h3,
          show n + 1 + d' = n + d + Q ^ 2 by rw [hdd]; omega, Nat.add_div_right _ hQpos,
          coeff_X_mul', if_neg (Nat.succ_ne_zero _), Nat.add_sub_cancel]
      · rw [if_neg (mt hdv.mp h3), if_neg h3]

lemma map_castInt_pgf : PowerSeries.map (Int.castRingHom ℤ) partitionGF = partitionGF := by
  ext n; simp

/-- **The eigen-relation at ℓ ∈ {29, 31}**, generic form. -/
theorem eigen_big (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (h13 : 13 ≤ ℓ) (hjj : ℓ = jj ℓ + 24)
    (hsf0 : Squarefree (24 - jj ℓ)) (D : DimOne.DimOneProp ℓ) (h24 : 24 * δ ℓ + 1 = ℓ ^ 2)
    (hw : wlam ℓ = halfWt ℓ) (a : PowerSeries ℤ) (ha : a ∈ intLattice ℓ) (ha1 : a.coeff 1 = 1)
    (c : ZMod ℓ) (hseed : U ℓ (Ψ ℓ (Dz ^ δ ℓ)) = C c * Ψ ℓ (Dz * a))
    (Q : ℕ) [hQ : Fact Q.Prime] (hQ5 : 5 ≤ Q) :
    ∃ ν : ZMod ℓ, TT ℓ Q (Ψ ℓ (Pser ℓ 1)) = C ν * Ψ ℓ (Pser ℓ 1) := by
  have hPs := Weaver.Pser_eq ℓ h24 (Dz * a) c hseed
  have ha0 : a.coeff 0 = 0 := EigenLift.coeff_zero_of_intLattice ha
  set A := coordOf ℓ a with hAdef
  have hA1 : A.coeff 1 = 1 := by rw [hAdef, EigenLift.coeff_one_coordOf a ha0, ha1]
  have hA0 : A.coeff 0 = 0 := EigenLift.coeff_zero_coordOf a ha0
  obtain ⟨ν, hν⟩ := EigenLiftJ.eigen_char0J h13 hsf0 hQ5 D ha (by rw [hA1]; exact one_ne_zero)
  rw [← hAdef, hA1, one_smul] at hν
  -- `Δ a P^ℓ = X · coordOf ℓ a`
  have hfP : Dz * a * partitionGF ^ ℓ = X * A := by
    rw [hAdef, coordOf, map_castInt_pgf]
    conv_lhs => rw [hjj, pow_add]
    have h1 : qfacInf ^ 24 * partitionGF ^ 24 = 1 := by
      rw [← mul_pow, qfac_mul_pgf, one_pow]
    calc Dz * a * (partitionGF ^ jj ℓ * partitionGF ^ 24)
        = X * (a * partitionGF ^ jj ℓ) * (qfacInf ^ 24 * partitionGF ^ 24) := by
          simp only [Dz]; ring
      _ = X * (a * partitionGF ^ jj ℓ) := by rw [h1, mul_one]
  refine ⟨(ν : ZMod ℓ), ?_⟩
  have hj24 : jj ℓ < 24 := Nat.mod_lt _ (by norm_num)
  have hTA : heckeHalf Q (jj ℓ) (halfWt ℓ) (heckeSign Q (halfWt ℓ)) (Ψ ℓ A) =
      C (ν : ZMod ℓ) * Ψ ℓ A := by
    rw [← map_heckeHalf, hν, map_zsmul, zsmul_eq_mul, ← map_intCast (C (R := ZMod ℓ))]
  have hΨA0 : coeff 0 (Ψ ℓ A) = 0 := by rw [coeff_map, hA0, map_zero]
  rw [hPs, hfP, map_mul, map_X, TT, hw, heckeHalf_C_mul,
    heckeHalf_X_mul Q hQ5 (jj ℓ) ℓ _ _ hjj hj24 _ hΨA0, hTA]
  ring

instance fact29 : Fact (Nat.Prime 29) := ⟨by norm_num⟩
instance fact31 : Fact (Nat.Prime 31) := ⟨by norm_num⟩

lemma coeff1_Dz_mul (g : PowerSeries ℤ) (hg : constantCoeff g = 1) : (Dz * g).coeff 1 = 1 := by
  rw [show Dz * g = X * (qfacInf ^ 24 * g) by simp only [Dz]; ring, coeff_succ_X_mul,
    coeff_zero_eq_constantCoeff_apply, map_mul, map_pow, hg, mul_one,
    ← coeff_zero_eq_constantCoeff_apply, MockTheta5.JTP.coeff_zero_qfacInf, one_pow]

lemma intLattice_of_form {ℓ : ℕ} [Fact ℓ.Prime] {a : PowerSeries ℤ} (ha : IntForm (kPrime ℓ) a)
    (ha0 : a.coeff 0 = 0) : a ∈ intLattice ℓ := by
  obtain ⟨F, hF⟩ := ha
  have hF0 : (UpperHalfPlane.qExpansion 1 F).coeff 0 = 0 := by
    rw [hF, PowerSeries.coeff_map, ha0, map_zero]
  exact ⟨ModularForm.toCuspForm F hF0, hF.symm⟩

/-- **`T(Q²) G ≡ ν G (mod 29)`** for every prime `Q ≥ 5`. -/
theorem eigen_29 (Q : ℕ) [Fact Q.Prime] (hQ5 : 5 ≤ Q) :
    ∃ ν : ZMod 29, TT 29 Q (Ψ 29 (Pser 29 1)) = C ν * Ψ 29 (Pser 29 1) := by
  have hf : FiniteArithmetic.Cert29.f = Dz * (Dz * RamanujanTau.Mod691.p4) := by
    simp only [FiniteArithmetic.Cert29.f]; ring
  have hc0 : constantCoeff RamanujanTau.Mod691.p4 = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, RamanujanTau.Mod691.coeff_p4]; simp
  have hform : IntForm (kPrime 29) (Dz * RamanujanTau.Mod691.p4) :=
    (IntForm.disc.mul IntForm.E4).cast (by decide)
  have h0 : (Dz * RamanujanTau.Mod691.p4).coeff 0 = 0 := by
    rw [coeff_zero_eq_constantCoeff_apply, map_mul]; simp [Dz]
  exact eigen_big 29 (by norm_num) (by decide)
    (by rw [show 24 - jj 29 = 19 by decide]; exact (Nat.Prime.prime (by norm_num)).squarefree)
    DimOne40.dimOne_29 (by decide)
    (by decide) _ (intLattice_of_form hform h0) (coeff1_Dz_mul _ hc0) 8
    (by rw [← hf]; exact FiniteArithmetic.Cert29.seed) Q hQ5

/-- **`T(Q²) G ≡ ν G (mod 31)`** for every prime `Q ≥ 5`. -/
theorem eigen_31 (Q : ℕ) [Fact Q.Prime] (hQ5 : 5 ≤ Q) :
    ∃ ν : ZMod 31, TT 31 Q (Ψ 31 (Pser 31 1)) = C ν * Ψ 31 (Pser 31 1) := by
  have hf : FiniteArithmetic.Cert31.f = Dz * (Dz * RamanujanTau.Mod691.p6) := by
    simp only [FiniteArithmetic.Cert31.f]; ring
  have hc0 : constantCoeff RamanujanTau.Mod691.p6 = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, RamanujanTau.Mod691.coeff_p6]; simp
  have hform : IntForm (kPrime 31) (Dz * RamanujanTau.Mod691.p6) :=
    (IntForm.disc.mul IntForm.E6).cast (by decide)
  have h0 : (Dz * RamanujanTau.Mod691.p6).coeff 0 = 0 := by
    rw [coeff_zero_eq_constantCoeff_apply, map_mul]; simp [Dz]
  exact eigen_big 31 (by norm_num) (by decide)
    (by rw [show 24 - jj 31 = 17 by decide]; exact (Nat.Prime.prime (by norm_num)).squarefree)
    DimOne40.dimOne_31 (by decide)
    (by decide) _ (intLattice_of_form hform h0) (coeff1_Dz_mul _ hc0) 10
    (by rw [← hf]; exact FiniteArithmetic.Cert31.seed) Q hQ5

/-- From `∃ ν` and one coefficient `N₀` with `G(N₀) ≢ 0`: the eigenvalue is the claimed one. -/
theorem eigen_of_exists (ℓ : ℕ) [Fact ℓ.Prime] (Q : ℕ) [Fact Q.Prime] (N0 : ℕ) (μ : ZMod ℓ)
    (hex : ∃ ν : ZMod ℓ, TT ℓ Q (Ψ ℓ (Pser ℓ 1)) = C ν * Ψ ℓ (Pser ℓ 1))
    (h : coeff N0 (TT ℓ Q (Ψ ℓ (Pser ℓ 1))) = μ * coeff N0 (Ψ ℓ (Pser ℓ 1)) ∧
      coeff N0 (Ψ ℓ (Pser ℓ 1)) ≠ 0) :
    TT ℓ Q (Ψ ℓ (Pser ℓ 1)) = C μ * Ψ ℓ (Pser ℓ 1) := by
  obtain ⟨ν, hν⟩ := hex
  have h1 := h.1
  rw [hν, coeff_C_mul] at h1
  have : ν = μ := mul_right_cancel₀ h.2 h1
  rw [hν, this]

end RamanujanTau.OnoWeaverMore
