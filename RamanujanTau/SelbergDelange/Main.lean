/-
# Toward Selberg–Delange for `R(s)^{−1/2}`: region bounds and the Rankin–Selberg PNT with error

See `docs/SELBERG_DELANGE.md`. Build: `nice -n 10 lake build RamanujanTau.SelbergDelange.Main`.

* `logDerivKK_bound`: `KK ≠ 0` and `‖KK'/KK(s)‖ ≤ C log²(|t|+2)` on `Re s ≥ 1 − c/log(|t|+2)`,
  `KK = (s−1)ζ(s)L(Sym²Δ,s)` (unconditional).
* `perron_shiftK`, `contour_boundK`, `smoothed_boundK`: Perron with the pole term
  `π x(1−1/x)²` and the contour shift into the region.
* `psiR_error`: `|Σ_{n≤x} vR(n) − x| ≤ K x exp(−b√log x)` for `x ≥ X₀` (unconditional,
  Deligne-free), `vR(p) = λ(p)² log p`.
* `rs_prime_PNT_error [DeligneBound]`: `|Σ_{p≤x} λ(p)² log p − x| ≤ K x exp(−b√log x)`.
-/
import RamanujanTau.SelbergDelange.PrimeDeligne

#print axioms RamanujanTau.SelbergDelange.norm_KK_le
#print axioms RamanujanTau.SelbergDelange.logDerivKK_right
#print axioms RamanujanTau.SelbergDelange.logDerivKK_bound
#print axioms RamanujanTau.SelbergDelange.regK_exists
#print axioms RamanujanTau.SelbergDelange.pole_integral
#print axioms RamanujanTau.SelbergDelange.perron_shiftK
#print axioms RamanujanTau.SelbergDelange.contour_boundK
#print axioms RamanujanTau.SelbergDelange.smoothed_boundK
#print axioms RamanujanTau.SelbergDelange.FR_bound
#print axioms RamanujanTau.SelbergDelange.diff_sandwich
#print axioms RamanujanTau.SelbergDelange.psiR_error
#print axioms RamanujanTau.SelbergDelange.vR_le_vonMangoldt
#print axioms RamanujanTau.SelbergDelange.rs_prime_PNT_error
