import RamanujanTau.EulerFactor

/-! # The general closed form `τ(p^r)` via Gegenbauer / Chebyshev-U polynomials

The Hecke recurrence `τ(p^{r+1}) = τ(p)·τ(p^r) − p¹¹·τ(p^{r-1})` makes `r ↦ τ(p^r)` a member of the
**Gegenbauer / Chebyshev-second-kind** polynomial family: the two-variable Dickson polynomials
`G_r(s,q)` defined by `G_0 = 1`, `G_1 = s`, `G_{r+2} = s·G_{r+1} − q·G_r`. With `(s,q) = (τ p, p¹¹)`
they compute every `τ(p^r)` at once — one theorem superseding the fixed-exponent forms
`τ(p²), …, τ(p⁷)`.

`gegen` is exactly the homogenization of the Chebyshev polynomial of the second kind `U_r`
(equivalently the Gegenbauer polynomial `C_r^{(1)}`), characterized by this three-term recurrence.
Its explicit coefficients are the Gegenbauer/Chebyshev binomials `(−1)^j C(r−j, j)` — the pattern the
proofworld pipeline discovered and the kernel verified for `r ≤ 7` in `HeckePowers`
(`τ(p⁴)=τp⁴−3p¹¹τp²+p²²`, `τ(p⁷)=τp⁷−6p¹¹τp⁵+10p²²τp³−4p³³τp`, …).
-/

namespace RamanujanTau

/-- Dickson/Gegenbauer recurrence family: `G_0 = 1`, `G_1 = s`, `G_{r+2} = s·G_{r+1} − q·G_r`.
This is the (homogenized) Chebyshev polynomial of the second kind `U_r`, i.e. the Gegenbauer
polynomial `C_r^{(1)}`. With `(s,q) = (τ p, p¹¹)` it equals `τ(p^r)`. -/
def gegen (s q : ℤ) : ℕ → ℤ
  | 0 => 1
  | 1 => s
  | (r + 2) => s * gegen s q (r + 1) - q * gegen s q r

@[simp] theorem gegen_zero (s q : ℤ) : gegen s q 0 = 1 := rfl
@[simp] theorem gegen_one (s q : ℤ) : gegen s q 1 = s := rfl

/-- The defining Gegenbauer/Chebyshev three-term recurrence. -/
theorem gegen_succ_succ (s q : ℤ) (r : ℕ) :
    gegen s q (r + 2) = s * gegen s q (r + 1) - q * gegen s q r := rfl

/-- **General closed form for `τ(p^r)`.** For every prime `p` and every `r`,
`τ(p^r) = G_r(τ p, p¹¹)` — the Gegenbauer/Chebyshev-U value. A single theorem giving all prime-power
values of `τ`, of which `tau_prime_sq`, `tau_prime_cube`, and `HeckePowers.τ(p⁴…p⁷)` are instances. -/
theorem tau_ppow_eq_gegen [TauHeckeRecurrence] {p : ℕ} (hp : p.Prime) (r : ℕ) :
    τ (p ^ r) = gegen (τ p) ((p : ℤ) ^ 11) r := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    rcases r with _ | _ | k
    · simp [tau_one]
    · simp
    · have hrec := euler_factor_coeff hp k                 -- τ(p^{k+2}) − τp·τ(p^{k+1}) + p¹¹·τ(p^k) = 0
      have e1 := ih (k + 1) (by omega)                      -- τ(p^{k+1}) = G_{k+1}
      have e0 := ih k (by omega)                            -- τ(p^k)     = G_k
      rw [show k + 1 + 1 = k + 2 from rfl, gegen_succ_succ, ← e1, ← e0]
      linarith

/-- Sanity: the general formula reproduces the proofworld/kernel-verified `τ(p²) = τ(p)² − p¹¹`. -/
example [TauHeckeRecurrence] {p : ℕ} (hp : p.Prime) :
    τ (p ^ 2) = gegen (τ p) ((p : ℤ) ^ 11) 2 := tau_ppow_eq_gegen hp 2

end RamanujanTau
