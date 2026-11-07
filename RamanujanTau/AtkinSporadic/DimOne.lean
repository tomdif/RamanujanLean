import RamanujanTau.AtkinSporadic.LevelSixPrecision
import RamanujanTau.TheoremA.SignLattice

/-!
# The `U₂, U₃`-eigenspace of `M_{2λ}(Γ₀(6))` is one-dimensional (finite certificate)

`DimOneProp ℓ`: every level-six form `b` of weight `2λ = ℓ − 3` with integral expansion,
`U₂ b = ε₂ b`, `U₃ b = ε₃ b` (`ε_p = (p/ℓ) p^{λ−1}`, the eigenvalues carried by every Shimura lift)
and `b(1) = 0` vanishes. So this eigenspace is (at most) one-dimensional, detected by `b(1)`.

The proof is a finite ℤ-linear-algebra certificate (`DimCert`): writing `b = Σ cᵢ Eᵢ` on the
repo's integral basis `Eᵢ = evenSeries λ i` (`TheoremA.even_expansion_descent`), a square set of
relations `Σᵢ L_{r,i} cᵢ = 0` (the coefficient `b(1)`, and `b(2m) = ε₂ b(m)`, `b(3m) = ε₃ b(m)`
for small `m`) is inverted by an integer matrix `K` with `K L = d·I`, `d ≠ 0`, checked by the
kernel. All basis coefficients involved lie in `q⁰ … q²⁸` (`LevelSixPrecision`).
-/

set_option autoImplicit false

namespace RamanujanTau.AtkinSporadic.DimOne
open PowerSeries ModularForm RamanujanTau.TheoremA RamanujanTau.TheoremA.SignLattice
open RamanujanTau.TheoremA.EtaSquared LevelSix UpperHalfPlane

/-- Certificate data: the eigenvalues, the basis lists, the chosen rows (kind, m) with kind
`0` = coefficient `m = 1`, `1` = `U₂` relation at `m`, `2` = `U₃` relation at `m`, the integer
left inverse `K` and the scalar `d`. -/
structure DimCert where
  e2 : ℤ
  e3 : ℤ
  basis : List (List ℤ)
  rows : List (ℕ × ℕ)
  K : List (List ℤ)
  d : ℤ

namespace DimCert
variable (C : DimCert)

def E (i j : ℕ) : ℤ := coeffList (C.basis.getD i []) j

def Lrow (r i : ℕ) : ℤ :=
  match C.rows.getD r (0, 0) with
  | (0, m) => C.E i m
  | (1, m) => C.E i (2 * m) - C.e2 * C.E i m
  | (_, m) => C.E i (3 * m) - C.e3 * C.E i m

def Kent (k r : ℕ) : ℤ := coeffList (C.K.getD k []) r

def rowOK : ℕ × ℕ → Bool
  | (0, m) => m == 1
  | (1, m) => decide (2 * m ≤ 28)
  | (_, m) => decide (3 * m ≤ 28)

end DimCert

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

/-- The eigenspace statement. -/
def DimOneProp : Prop :=
  ∀ (b : PowerSeries ℤ) (g : Forms ℓ),
    PowerSeries.map (Int.castRingHom ℂ) b = qExpansion 1 g →
    BoylanWebb.U 2 b = eig2 ℓ • b → BoylanWebb.U 3 b = eig3 ℓ • b → b.coeff 1 = 0 → b = 0

variable {ℓ}

omit hℓ in
lemma coeff_ser (c : Fin (2 * halfWt ℓ + 1) → ℤ) (j : ℕ) :
    (ser ℓ c).coeff j = ∑ i : Fin (2 * halfWt ℓ + 1), c i * (evenSeries (halfWt ℓ) i.val).coeff j := by
  simp only [ser, evenCombination, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

/-- **Soundness of the certificate.** -/
theorem DimCert.sound (C : DimCert) (he2 : eig2 ℓ = C.e2) (he3 : eig3 ℓ = C.e3)
    (hb : ∀ i : Fin (2 * halfWt ℓ + 1), C.basis.getD i [] = basisL (halfWt ℓ) i)
    (hr : ∀ r : Fin (2 * halfWt ℓ + 1), DimCert.rowOK (C.rows.getD r (0, 0)) = true)
    (hc : ∀ k i : Fin (2 * halfWt ℓ + 1),
      ∑ r : Fin (2 * halfWt ℓ + 1), C.Kent k r * C.Lrow r i = if k = i then C.d else 0)
    (hd : C.d ≠ 0) : DimOneProp ℓ := by
  intro b g hg hU2 hU3 h1
  set c := lat ℓ b with hcdef
  have hsc : ser ℓ c = b := ser_lat ℓ hg
  -- coefficients through `q²⁸`
  have hE : ∀ j, j < 29 → b.coeff j = ∑ i : Fin (2 * halfWt ℓ + 1), C.E i j * c i := by
    intro j hj
    rw [← hsc, coeff_ser]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [DimCert.E, hb i, evenSeries_coeff28 _ _ (by omega) hj, mul_comm]
  have hU2' : ∀ m, b.coeff (2 * m) = eig2 ℓ * b.coeff m := by
    intro m
    have := congrArg (PowerSeries.coeff m) hU2
    rwa [BoylanWebb.coeff_U, map_zsmul, smul_eq_mul] at this
  have hU3' : ∀ m, b.coeff (3 * m) = eig3 ℓ * b.coeff m := by
    intro m
    have := congrArg (PowerSeries.coeff m) hU3
    rwa [BoylanWebb.coeff_U, map_zsmul, smul_eq_mul] at this
  -- every chosen row annihilates `c`
  have hrow : ∀ r : Fin (2 * halfWt ℓ + 1),
      ∑ i : Fin (2 * halfWt ℓ + 1), C.Lrow r i * c i = 0 := by
    intro r
    have hok := hr r
    rcases hx : C.rows.getD r (0, 0) with ⟨κ, m⟩
    rw [hx] at hok
    simp only [DimCert.Lrow, hx]
    rcases κ with _ | _ | κ
    · simp only [DimCert.rowOK, beq_iff_eq] at hok
      subst hok
      rw [← hE 1 (by norm_num), h1]
    · simp only [DimCert.rowOK, decide_eq_true_eq] at hok
      have e1 := hE (2 * m) (by omega)
      have e2 := hE m (by omega)
      simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
      rw [← e1, ← e2, hU2', he2, sub_self]
    · simp only [DimCert.rowOK, decide_eq_true_eq] at hok
      have e1 := hE (3 * m) (by omega)
      have e2 := hE m (by omega)
      simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
      rw [← e1, ← e2, hU3', he3, sub_self]
  -- invert
  have hc0 : c = 0 := by
    funext k
    have hk : C.d * c k = 0 := by
      calc C.d * c k = ∑ i : Fin (2 * halfWt ℓ + 1), (if k = i then C.d else 0) * c i := by
            rw [Finset.sum_eq_single k (fun i _ hi => by rw [if_neg (Ne.symm hi), zero_mul])
              (fun h => absurd (Finset.mem_univ k) h), if_pos rfl]
        _ = ∑ i : Fin (2 * halfWt ℓ + 1), (∑ r : Fin (2 * halfWt ℓ + 1),
              C.Kent k r * C.Lrow r i) * c i := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hc k i]
        _ = ∑ r : Fin (2 * halfWt ℓ + 1), C.Kent k r *
              ∑ i : Fin (2 * halfWt ℓ + 1), C.Lrow r i * c i := by
            simp only [Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun i _ => ?_
            ring
        _ = 0 := by simp [hrow]
    exact (mul_eq_zero.mp hk).resolve_left hd
  rw [← hsc, hc0]
  exact map_zero (evenCombinationLinear (halfWt ℓ))

end RamanujanTau.AtkinSporadic.DimOne
