/-
# Atkin–O'Brien: the formalizable content of the proofs of (I2) and (I3)

`docs/ATKIN_OBRIEN_PROOF.md`, "Proof of I2 and I3". Notation: `P = (q;q)_∞`, `V = (q ↦ q^p)`,
`A_p = P^{2p}/(VP)²`, `Q = E/A_p`, `Δ = q·P²⁴`.

**Formalized here:**
* the q-series identities: `Q^{12} = E^{12}·VΔ/Δ^p` (cleared of denominators);
* the congruence `A_p ≡ 1 (mod p)`, hence `Q ≡ 1` whenever `E ≡ 1`;
* the Newton-polygon break `v < p/(p+1)`;
* both regimes of the cross-check `v(Lie π̌) = v`;
* the pointwise cancellation `v(Q(x)) = 0`;
* the passage from "integral for every `ρ < p/(p+1)`" to `v(a_i) ≥ ⌈pi/(p+1)⌉`;
* the radius arithmetic behind I3.

**Not formalized:** the geometric facts. These are the existence of the canonical subgroup and the
torsion valuations from the Newton polygon (Katz 3.10.7), Lubin's quotient with its Néron differential, and
the reducedness of Katz's integral model. Mathlib has no formal groups of elliptic curves, Néron models,
modular curves or rigid spaces.
-/
import RamanujanTau.TauCongruences

set_option autoImplicit false

namespace AtkinOBrien.I2
open PowerSeries MockTheta5.JTP TauCong
open RankProof (Ea Ea_X)

variable (p : ℕ) [hp : Fact p.Prime]

local notation "P" => (qfacInf : PowerSeries ℤ)

lemma hp0 : p ≠ 0 := hp.out.ne_zero

/-- `VΔ = q^p · (VP)²⁴`. -/
lemma V_Delta : Ea p (hp0 p) (X * P ^ 24) = X ^ p * (Ea p (hp0 p) P) ^ 24 := by
  rw [map_mul, map_pow, Ea_X]

/-- **`Q^{12} = E^{12}·VΔ/Δ^p`**, cleared: `(E·(VP)²)^{12}·Δ^p = E^{12}·VΔ·(P^{2p})^{12}`.
(`Q = E·(VP)²/P^{2p}`.) -/
theorem Q12_identity (E : PowerSeries ℤ) :
    (E * (Ea p (hp0 p) P) ^ 2) ^ 12 * (X * P ^ 24) ^ p =
      E ^ 12 * Ea p (hp0 p) (X * P ^ 24) * (P ^ (2 * p)) ^ 12 := by
  rw [V_Delta]; ring

/-- **`A_p ≡ 1 (mod p)`**: `P^{2p} ≡ (VP)² (mod p)`. -/
theorem Ap_cong : Ψ p (P ^ (2 * p)) = Ψ p ((Ea p (hp0 p) P) ^ 2) := by
  have h := frob_qfacInf p 1
  simp only [pow_one] at h
  rw [map_pow, map_pow, mul_comm, pow_mul, h]

/-- **`Q ≡ 1 (mod p)`** given `E ≡ 1 (mod p)`, cleared: `E·(VP)² ≡ P^{2p}`. -/
theorem Q_cong (E : PowerSeries ℤ) (hE : Ψ p E = 1) :
    Ψ p (E * (Ea p (hp0 p) P) ^ 2) = Ψ p (P ^ (2 * p)) := by
  rw [map_mul, hE, one_mul, Ap_cong]

end AtkinOBrien.I2

namespace AtkinOBrien.I2Val

/-- **Newton polygon break**: the first slope `(1−v)/(p−1)` of `[p](T)/T` exceeds the second `v/(p(p−1))`
iff `v < p/(p+1)`. -/
theorem newton_break (p v : ℚ) (hp : 1 < p) :
    v / (p * (p - 1)) < (1 - v) / (p - 1) ↔ v < p / (p + 1) := by
  have h1 : 0 < p - 1 := by linarith
  have h2 : 0 < p * (p - 1) := by positivity
  rw [div_lt_div_iff₀ h2 h1, lt_div_iff₀ (by linarith)]
  constructor <;> intro h <;> nlinarith

/-- `v(Lie π̌) = v`, **non-canonical regime** `v < 1/(p+1)`: `ker π̌` is a non-canonical subgroup of
`E/H`, with `v(E/H) = p·v`. Its `p−1` nonzero points have valuation `pv/(p²−p)`. -/
theorem lie_dual_noncanonical (p v : ℚ) (hp : 1 < p) : (p - 1) * (p * v / (p ^ 2 - p)) = v := by
  have h1 : p - 1 ≠ 0 := by linarith
  have h0 : p ≠ 0 := by linarith
  rw [show p ^ 2 - p = p * (p - 1) by ring]
  field_simp

/-- `v(Lie π̌) = v`, **canonical regime** `1/(p+1) < v < p/(p+1)`: `v(E/H) = 1 − v`. -/
theorem lie_dual_canonical (v : ℚ) : 1 - (1 - v) = v := by ring

/-- `v(Lie π) + v(Lie π̌) = v(p) = 1`, with `v(Lie π) = (p−1)·(1−v)/(p−1)`. -/
theorem lie_sum (p v : ℚ) (hp : 1 < p) : (p - 1) * ((1 - v) / (p - 1)) + v = 1 := by
  have : p - 1 ≠ 0 := by linarith
  field_simp; ring

/-- **pointwise cancellation**. If `v(E(x)) = v` and `v(λ) = v`, and both `Δ` values are units, then
`v(Q^{12}(x)) = 12·v(E) + (−12·v(λ) + v(Δ') − p·v(Δ)) = 0`. -/
theorem Q_val (v vl vΔ vΔ' : ℚ) (p : ℚ) (hl : vl = v) (hΔ : vΔ = 0) (hΔ' : vΔ' = 0) :
    12 * v + (-12 * vl + vΔ' - p * vΔ) = 0 := by
  subst hl hΔ hΔ'; ring

/-- **from all radii to the sharp bound**. If an integer `n` satisfies `i·ρ ≤ n` for every rational
`0 ≤ ρ < p/(p+1)`, then `⌈p i/(p+1)⌉ ≤ n`. -/
theorem sharp_of_all_radii (p : ℕ) (hp : 1 ≤ p) (i : ℕ) (n : ℤ)
    (h : ∀ ρ : ℚ, 0 ≤ ρ → ρ < (p : ℚ) / (p + 1) → (i : ℚ) * ρ ≤ n) :
    ⌈((p : ℚ) * i) / (p + 1)⌉ ≤ n := by
  rw [Int.ceil_le]
  have hp' : (1 : ℚ) ≤ p := by exact_mod_cast hp
  have hp1 : (0 : ℚ) < p + 1 := by linarith
  set t : ℚ := (p : ℚ) / (p + 1) with ht_def
  have ht0 : 0 < t := by positivity
  have hn0 : (0 : ℚ) ≤ n := by simpa using h 0 le_rfl ht0
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simpa using hn0
  have hi' : (0 : ℚ) < i := by exact_mod_cast hi
  by_contra hlt
  rw [not_le, show (p : ℚ) * i / (p + 1) = t * i by rw [ht_def]; ring] at hlt
  have hn : (n : ℚ) / i < t := by rw [div_lt_iff₀ hi']; linarith
  have hni : 0 ≤ (n : ℚ) / i := div_nonneg hn0 hi'.le
  have key := h (((n : ℚ) / i + t) / 2) (by positivity) (by linarith)
  have : (n : ℚ) / i < ((n : ℚ) / i + t) / 2 := by linarith
  rw [div_lt_iff₀ hi'] at this
  nlinarith

/-- **I3 radius arithmetic**: if `v(E) ≤ ρ < 1/(p+1)` then `v(E/H) = p·v(E) ≤ pρ`, and `pρ < p/(p+1)`
(so the target lies in the canonical region). -/
theorem I3_radius (p v ρ : ℚ) (hp : 0 < p) (hv : v ≤ ρ) (hρ : ρ < 1 / (p + 1)) :
    p * v ≤ p * ρ ∧ p * ρ < p / (p + 1) := by
  refine ⟨by nlinarith, ?_⟩
  have : p * ρ < p * (1 / (p + 1)) := by nlinarith
  simpa [mul_one_div] using this

end AtkinOBrien.I2Val
