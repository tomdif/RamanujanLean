import RamanujanTau.AtkinSporadic.Atkin13

/-!
# Atkin's congruences modulo 13 in the twisted class

Instances of `Atkin13.twisted_hecke` / `vanish_of_eigen` at `Q = 11` and `Q = 37`, each with one
kernel certificate on `p(N) mod 13` for `N < 1700` resp. `N < 19200`.

* **`atkin_13`**: `13 ∣ p(17303 n + 237)` (Atkin 1968), given `EtaHecke 11 168 1`.
* `atkin_13_class`: `13 ∣ p(N)` whenever `24N − 1 = 11² m` with `(m/11) = 1`, `(m/13) = −1`.
* `atkin_13_Q37_class`: `13 ∣ p(N)` whenever `24N − 1 = 37² m` with `(m/37) = −1`, `(m/13) = −1`.
-/

set_option autoImplicit false

namespace RamanujanTau.AtkinSporadic.Atkin13
open PowerSeries BoylanWebb
open RamanujanTau.FiniteArithmetic
open Twist13

instance fact11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩
instance fact37 : Fact (Nat.Prime 37) := ⟨by norm_num⟩

/-! ### `Q = 11`, eigenvalue `3` -/

theorem chk11 : chk 11 3 1700 33 = true := by decide +kernel

theorem eigen11 (H : EtaHeckeMod 13 11 168 1) :
    heckeHalf 11 1 167 (heckeSign 11 167) (Ψ 13 twPGF) = PowerSeries.C 3 * Ψ 13 twPGF :=
  twisted_hecke 11 (by norm_num) 3 1700 33 (by norm_num) (by norm_num) (by decide) (by norm_num)
    chk11 H

theorem sign11 : heckeSign 11 167 = -1 := by
  rw [heckeSign, legendreSym_val 11 (by norm_num), legendreSym_val 11 (by norm_num)]
  decide

/-- **The thirty vanishing classes modulo `17303`.** -/
theorem atkin_13_class (H : EtaHeckeMod 13 11 168 1) (N m : ℕ) (hm : 24 * N = 11 ^ 2 * m + 1)
    (h11 : legendreSym 11 m = 1) (h13 : legendreSym 13 m = -1) :
    13 ∣ Fintype.card (Nat.Partition N) :=
  vanish_of_eigen 11 (by norm_num) 3 (by decide) (eigen11 H) 1 one_ne_zero
    (by rw [sign11]; decide) (by norm_num) N m hm h11 h13

/-- **Atkin (1968): `p(11³·13·n + 237) ≡ 0 (mod 13)`**, conditional on `EtaHecke 11 168 1`. -/
theorem atkin_13 (H : EtaHeckeMod 13 11 168 1) (n : ℕ) :
    13 ∣ Fintype.card (Nat.Partition (17303 * n + 237)) := by
  refine atkin_13_class H _ (3432 * n + 47) (by ring) ?_ ?_
  · rw [legendreSym.mod, show ((3432 * n + 47 : ℕ) : ℤ) % (11 : ℕ) = 3 by push_cast; omega,
      legendreSym_val 11 (by norm_num)]
    decide
  · rw [legendreSym.mod, show ((3432 * n + 47 : ℕ) : ℤ) % (13 : ℕ) = 8 by push_cast; omega,
      legendreSym_val 13 (by norm_num)]
    decide

/-! ### `Q = 37`, eigenvalue `3` -/

theorem chk37 : chk 37 3 19200 113 = true := by decide +kernel

theorem eigen37 (H : EtaHeckeMod 13 37 168 1) :
    heckeHalf 37 1 167 (heckeSign 37 167) (Ψ 13 twPGF) = PowerSeries.C 3 * Ψ 13 twPGF :=
  twisted_hecke 37 (by norm_num) 3 19200 113 (by norm_num) (by norm_num) (by decide) (by norm_num)
    chk37 H

theorem sign37 : heckeSign 37 167 = 1 := by
  rw [heckeSign, legendreSym_val 37 (by norm_num), legendreSym_val 37 (by norm_num)]
  decide

/-- `13 ∣ p(N)` whenever `24N − 1 = 37² m`, `(m/37) = −1`, `(m/13) = −1`. -/
theorem atkin_13_Q37_class (H : EtaHeckeMod 13 37 168 1) (N m : ℕ) (hm : 24 * N = 37 ^ 2 * m + 1)
    (h37 : legendreSym 37 m = -1) (h13 : legendreSym 13 m = -1) :
    13 ∣ Fintype.card (Nat.Partition N) :=
  vanish_of_eigen 37 (by norm_num) 3 (by decide) (eigen37 H) (-1) (by norm_num)
    (by rw [sign37]; decide) (by norm_num) N m hm h37 h13

end RamanujanTau.AtkinSporadic.Atkin13
