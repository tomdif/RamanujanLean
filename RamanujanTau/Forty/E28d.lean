/-
# Entry 3.28(ii): the algebra of Yesilyurt's §3 ((3.29)–(3.44)) in an abstract field

Source: H. Yesilyurt, *Elementary proofs of some identities of Ramanujan for the Rogers–Ramanujan functions*,
J. Math. Anal. Appl. 388 (2012) 420–434, §3.

Variables (at the nome `q`, `Q = q¹⁷`):
`a1 = χ(q)`, `a2 = χ(−q)`, `b1 = χ(Q)`, `b2 = χ(−Q)` (so `c = a1a2 = χ(−q²)`, `d = b1b2 = χ(−Q²)`),
`e1 = χ(q²)`, `e2 = χ(Q²)`, `U = U(q)`, `Um = U(−q)`, `V = V(q)`, `Vm = V(−q)`, `Uq = U(q²)`, `Vq = V(q²)`,
`Um2 = U(−q²)`, `Vm2 = V(−q²)`, `U4 = U(q⁴)`, `V4 = V(q⁴)`.

Hypotheses: Entry 3.28(i) (`U/V = χ(−q)/χ(−Q)`) at `q, −q, q², −q², q⁴`; his (3.1) at `±q`, (3.2), (3.4), (3.5),
(3.6) at `q`, `−q`, `q²`; and the branch condition (the root of (3.39) that is chosen at (3.40)).
Conclusion: his (3.8) at `q²`, cleared.
-/
import Mathlib

set_option autoImplicit false

namespace Forty

/-- The core of (3.29)–(3.41): with `s1 = S(q)`, `s2 = S(−q)`, `P = S(q²)`, `t = T(q²)`, `Z = S(−q²)S(q⁴)` and the
square root `R` of `s1 s2 Z`, the relations (3.5), (3.6) at `q²`, (3.34), (3.29) give `(P² − R)² = 4q⁴` (his (3.39)). -/
theorem core28 {K : Type*} [Field K] (q s1 s2 P R Z t : K) (ht : t ≠ 0)
    (hA : s1 * s2 * t - P * t = 4 * q ^ 4)
    (hB : Z - q ^ 2 * P = t)
    (hC : R ^ 2 = s1 * s2 * Z)
    (hD : (2 * s1 * s2 * P - q * (s1 ^ 2 - s2 ^ 2) - 2 * R) * t = 4 * q ^ 4 * P)
    (hF : s1 * s2 * (P ^ 2 - q ^ 2) - q * P * (s1 ^ 2 - s2 ^ 2) = t) :
    (P ^ 2 - R) ^ 2 = 4 * q ^ 4 ∧
      P ^ 3 * t + q ^ 2 * P * t + t ^ 2 + 4 * q ^ 6 = 2 * P * R * t := by
  have G38 : P ^ 3 * t + q ^ 2 * P * t + t ^ 2 + 4 * q ^ 6 = 2 * P * R * t := by
    linear_combination P * hD - t * hF - (P ^ 2 + q ^ 2) * hA
  refine ⟨?_, G38⟩
  apply mul_left_cancel₀ ht
  linear_combination t * hC + Z * hA + (P * t + 4 * q ^ 4) * hB + P * G38

/-- the abstract form of Yesilyurt's §3 from (3.29) to (3.8). -/
theorem alg28 {K : Type*} [Field K]
    (q a1 a2 b1 b2 e1 e2 U Um V Vm Uq Vq Um2 Vm2 U4 V4 : K)
    (hq : q ≠ 0) (ha1 : a1 ≠ 0) (ha2 : a2 ≠ 0) (hb1 : b1 ≠ 0) (hb2 : b2 ≠ 0) (he1 : e1 ≠ 0) (he2 : e2 ≠ 0) (h2' : (2 : K) ≠ 0)
    (h14 : U * b2 = V * a2) (h14m : Um * b1 = Vm * a1) (h14q : Uq * (b1 * b2) = Vq * (a1 * a2))
    (h14m2 : Um2 * e2 = Vm2 * e1) (h14q4 : U4 * (e2 * (b1 * b2)) = V4 * (e1 * (a1 * a2)))
    (h1 : a1 * a2 * (b1 * b2) * b2 * U = b1 * (b1 * b2) - q ^ 2 * a1 * (a1 * a2))
    (h1m : a1 * a2 * (b1 * b2) * b1 * Um = b2 * (b1 * b2) - q ^ 2 * a2 * (a1 * a2))
    (h2 : 2 * q * Vq = b1 * b2 * (a1 * b2 - a2 * b1))
    (h4 : 2 * (Um2 * V4) = b1 * b2 * (a1 * b2 + a2 * b1))
    (h5 : (U * V * (Um * Vm) - Uq * Vq) * (a1 * a2 * (b1 * b2)) ^ 2 = 4 * q ^ 4)
    (h6 : Um * Vm * (Uq * Vq) - q * (U * V) = a2 ^ 2 * b2 ^ 2)
    (h6m : U * V * (Uq * Vq) + q * (Um * Vm) = a1 ^ 2 * b1 ^ 2)
    (h6q2 : Um2 * Vm2 * (U4 * V4) - q ^ 2 * (Uq * Vq) = (a1 * a2 * (b1 * b2)) ^ 2)
    (hbr : ((Uq * Vq) ^ 2 + 2 * q ^ 2) * (b1 * b2) - a1 * a2 * (V * Vm) * (Um2 * V4) ≠ 0) :
    ((Uq * Vq) ^ 4 - q ^ 2 * (Uq * Vq) ^ 2) * (a1 * a2 * (b1 * b2)) ^ 3 =
      ((b1 * b2) ^ 3 + q ^ 4 * (a1 * a2) ^ 3) ^ 2 := by
  have hc : a1 * a2 ≠ 0 := mul_ne_zero ha1 ha2
  have hd : b1 * b2 ≠ 0 := mul_ne_zero hb1 hb2
  -- explicit forms (the parametrisation by `a1, a2, b1, b2`)
  have eU : U = (b1 * (b1 * b2) - q ^ 2 * a1 * (a1 * a2)) / (a1 * a2 * (b1 * b2) * b2) := by
    rw [eq_div_iff (mul_ne_zero (mul_ne_zero hc hd) hb2)]; linear_combination h1
  have eUm : Um = (b2 * (b1 * b2) - q ^ 2 * a2 * (a1 * a2)) / (a1 * a2 * (b1 * b2) * b1) := by
    rw [eq_div_iff (mul_ne_zero (mul_ne_zero hc hd) hb1)]; linear_combination h1m
  have eV : V = U * b2 / a2 := by rw [eq_div_iff ha2]; linear_combination -h14
  have eVm : Vm = Um * b1 / a1 := by rw [eq_div_iff ha1]; linear_combination -h14m
  have eVq : Vq = b1 * b2 * (a1 * b2 - a2 * b1) / (2 * q) := by
    rw [eq_div_iff (mul_ne_zero h2' hq)]; linear_combination h2
  have eUq : Uq = Vq * (a1 * a2) / (b1 * b2) := by rw [eq_div_iff hd]; linear_combination h14q
  have eW : Um2 * V4 = b1 * b2 * (a1 * b2 + a2 * b1) / 2 := by rw [eq_div_iff h2']; linear_combination h4
  -- abbreviations, written out: `c = a1a2`, `d = b1b2`, `W = U(−q²)V(q⁴)`, `t = T(q²) = (cd)²`,
  -- `Z = S(−q²)S(q⁴)`, `R = c V(q)V(−q) W / d` (the square root in (3.35))
  have htn : (a1 * a2 * (b1 * b2)) ^ 2 ≠ 0 := pow_ne_zero 2 (mul_ne_zero hc hd)
  -- `Z d = W² c`
  have kZ : Um2 * Vm2 * (U4 * V4) * (b1 * b2) = (Um2 * V4) ^ 2 * (a1 * a2) := by
    have k : (Vm2 * U4 * (b1 * b2) - Um2 * V4 * (a1 * a2)) * (e1 * e2) = 0 := by
      linear_combination (Vm2 * e1) * h14q4 - (V4 * e1 * (a1 * a2)) * h14m2
    have k' := (mul_eq_zero.mp k).resolve_right (mul_ne_zero he1 he2)
    linear_combination (Um2 * V4) * k'
  have k14 : U * Um * (b1 * b2) = V * Vm * (a1 * a2) := by
    linear_combination (Um * b1) * h14 + (V * a2) * h14m
  have eRd : a1 * a2 * (V * Vm) * (Um2 * V4) / (b1 * b2) * (b1 * b2) = a1 * a2 * (V * Vm) * (Um2 * V4) :=
    div_mul_cancel₀ _ hd
  have hC : (a1 * a2 * (V * Vm) * (Um2 * V4) / (b1 * b2)) ^ 2 = U * V * (Um * Vm) * (Um2 * Vm2 * (U4 * V4)) := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hd)
    linear_combination (a1 * a2 * (V * Vm) * (Um2 * V4) / (b1 * b2) * (b1 * b2) + a1 * a2 * (V * Vm) * (Um2 * V4)) * eRd
      - (U * V * Um * Vm * (b1 * b2)) * kZ - (V * Vm * (Um2 * V4) ^ 2 * (a1 * a2)) * k14
  -- (3.16) × (3.31) and (3.33): `T(−q) s2 + T(q) s1 − 2R = 4q⁴P/t`
  have hId : (a1 ^ 2 * b1 ^ 2 * (Um * Vm) + a2 ^ 2 * b2 ^ 2 * (U * V)
      - 2 * (a1 * a2 * (V * Vm) * (Um2 * V4) / (b1 * b2))) * (a1 * a2 * (b1 * b2)) ^ 2 = 4 * q ^ 4 * (Uq * Vq) := by
    rw [eW, eUq, eVq, eV, eVm, eU, eUm]
    field_simp
    ring
  have hD : (2 * (U * V) * (Um * Vm) * (Uq * Vq) - q * ((U * V) ^ 2 - (Um * Vm) ^ 2)
      - 2 * (a1 * a2 * (V * Vm) * (Um2 * V4) / (b1 * b2))) * (a1 * a2 * (b1 * b2)) ^ 2 = 4 * q ^ 4 * (Uq * Vq) := by
    linear_combination hId + (a1 * a2 * (b1 * b2)) ^ 2 * (Um * Vm) * h6m + (a1 * a2 * (b1 * b2)) ^ 2 * (U * V) * h6
  have hF : U * V * (Um * Vm) * ((Uq * Vq) ^ 2 - q ^ 2) - q * (Uq * Vq) * ((U * V) ^ 2 - (Um * Vm) ^ 2) =
      (a1 * a2 * (b1 * b2)) ^ 2 := by
    linear_combination (U * V * (Uq * Vq) + q * (Um * Vm)) * h6 + a2 ^ 2 * b2 ^ 2 * h6m
  have hA : U * V * (Um * Vm) * (a1 * a2 * (b1 * b2)) ^ 2 - Uq * Vq * (a1 * a2 * (b1 * b2)) ^ 2 = 4 * q ^ 4 := by
    linear_combination h5
  have hB : Um2 * Vm2 * (U4 * V4) - q ^ 2 * (Uq * Vq) = (a1 * a2 * (b1 * b2)) ^ 2 := h6q2
  obtain ⟨h39, h38⟩ := core28 q (U * V) (Um * Vm) (Uq * Vq) (a1 * a2 * (V * Vm) * (Um2 * V4) / (b1 * b2))
    (Um2 * Vm2 * (U4 * V4)) ((a1 * a2 * (b1 * b2)) ^ 2) htn hA hB hC hD hF
  -- the branch (3.40): `R = P² − 2q²`
  have hbr' : (Uq * Vq) ^ 2 + 2 * q ^ 2 - a1 * a2 * (V * Vm) * (Um2 * V4) / (b1 * b2) ≠ 0 := by
    intro h0
    apply hbr
    linear_combination (b1 * b2) * h0 + eRd
  have h40 : a1 * a2 * (V * Vm) * (Um2 * V4) / (b1 * b2) = (Uq * Vq) ^ 2 - 2 * q ^ 2 := by
    have hm : ((Uq * Vq) ^ 2 - a1 * a2 * (V * Vm) * (Um2 * V4) / (b1 * b2) - 2 * q ^ 2) *
        ((Uq * Vq) ^ 2 + 2 * q ^ 2 - a1 * a2 * (V * Vm) * (Um2 * V4) / (b1 * b2)) = 0 := by
      linear_combination h39
    have := (mul_eq_zero.mp hm).resolve_right hbr'
    linear_combination -this
  -- (3.41): `(P³ − 5q²P) t = t² + 4q⁶`
  have h41 : ((Uq * Vq) ^ 3 - 5 * q ^ 2 * (Uq * Vq)) * (a1 * a2 * (b1 * b2)) ^ 2 =
      ((a1 * a2 * (b1 * b2)) ^ 2) ^ 2 + 4 * q ^ 6 := by
    rw [h40] at h38; linear_combination -h38
  -- (3.42)–(3.44): `(d³ + q⁴c³)² t = c³d³ (s1 s2 t² + 4q² R t + 4q⁴ Z)`, with `Z = W²c/d`
  have h44 : ((b1 * b2) ^ 3 + q ^ 4 * (a1 * a2) ^ 3) ^ 2 * (a1 * a2 * (b1 * b2)) ^ 2 =
      (a1 * a2) ^ 3 * (b1 * b2) ^ 3 * (U * V * (Um * Vm) * ((a1 * a2 * (b1 * b2)) ^ 2) ^ 2
        + 4 * q ^ 2 * (a1 * a2 * (V * Vm) * (Um2 * V4) / (b1 * b2)) * (a1 * a2 * (b1 * b2)) ^ 2
        + 4 * q ^ 4 * ((Um2 * V4) ^ 2 * (a1 * a2) / (b1 * b2))) := by
    rw [eW, eV, eVm, eU, eUm]
    field_simp
    ring
  have eZ : Um2 * Vm2 * (U4 * V4) = (Um2 * V4) ^ 2 * (a1 * a2) / (b1 * b2) := by
    rw [eq_div_iff hd]; linear_combination kZ
  rw [h40, ← eZ] at h44
  apply mul_left_cancel₀ htn
  linear_combination -h44 - ((a1 * a2) ^ 3 * (b1 * b2) ^ 3 * (a1 * a2 * (b1 * b2)) ^ 2) * hA
    - (4 * q ^ 4 * (a1 * a2) ^ 3 * (b1 * b2) ^ 3) * hB
    + ((a1 * a2) ^ 3 * (b1 * b2) ^ 3 * (Uq * Vq)) * h41

end Forty
