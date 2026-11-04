import RamanujanTau.AtkinSporadic.Atkin13Main
import RamanujanTau.HalfHecke.EtaHecke

/-!
# Atkin's congruence modulo 13, unconditionally

`HalfHecke.etaHecke_11_168` / `etaHecke_37_168` prove the hypotheses `EtaHecke 11 168 1` and
`EtaHecke 37 168 1` (the Hecke operator `T(Q²)` on `η^{−1}S₁₆₈(SL₂ℤ)`, built as a coset sum and
shown modular via Petersson's `η`-multiplier and the sign of the quadratic Gauss sum).
-/

set_option autoImplicit false

namespace RamanujanTau.AtkinSporadic.Atkin13

/-- **Atkin (1968): `13 ∣ p(17303 n + 237)` for every `n`.** -/
theorem atkin_13_unconditional (n : ℕ) :
    13 ∣ Fintype.card (Nat.Partition (17303 * n + 237)) :=
  atkin_13 HalfHecke.etaHeckeMod_13_11 n

/-- The thirty classes modulo `17303`: `24N − 1 = 11²m`, `(m/11) = 1`, `(m/13) = −1`. -/
theorem atkin_13_class_unconditional (N m : ℕ) (hm : 24 * N = 11 ^ 2 * m + 1)
    (h11 : legendreSym 11 m = 1) (h13 : legendreSym 13 m = -1) :
    13 ∣ Fintype.card (Nat.Partition N) :=
  atkin_13_class HalfHecke.etaHeckeMod_13_11 N m hm h11 h13

/-- `24N − 1 = 37²m`, `(m/37) = −1`, `(m/13) = −1`. -/
theorem atkin_13_Q37_class_unconditional (N m : ℕ) (hm : 24 * N = 37 ^ 2 * m + 1)
    (h37 : legendreSym 37 m = -1) (h13 : legendreSym 13 m = -1) :
    13 ∣ Fintype.card (Nat.Partition N) :=
  atkin_13_Q37_class HalfHecke.etaHeckeMod_13_37 N m hm h37 h13

end RamanujanTau.AtkinSporadic.Atkin13
