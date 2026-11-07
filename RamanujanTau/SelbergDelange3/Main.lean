/-
# Selberg–Delange for the coefficients of `R(s)^{−1/2}` (unconditional)

See `docs/SELBERG_DELANGE.md` §8. Build: `nice -n 10 lake build RamanujanTau.SelbergDelange3.Main`.

* `mertens_vR_err`, `mertens_LamR_err`: `Σ_{m≤y} ΛR(m)/m = log y + c + O(1/log y)` (from `psiR_error`).
* `recF`, `recF_log`, `abs_recF_le`: the function with prescribed von Mangoldt function; majorant.
* `density_nonneg`: `Σ_{n≤y} F(n) ≪ y(log y)^{σ−1}` for `F ≥ 0` with Mertens-upper `Λ_F`.
* `fR = recF(−ΛR/2)` (coefficients of `R^{−1/2}`), `fR_one`, `fR_prime : fR p = −λ(p)²/2`.
* `logmean_fR`, `logmean_fR_log`: `Σ_{n≤x} fR(n)/n = C₁(log x)^{−1/2} + O(log log x (log x)^{−3/2})`.
* `logmean_LSD_log`: the general theorem with main term `C₁ (log x)^κ`.
* `selberg_sum_fR`: `Σ_{n≤x} (fR(n)/n) log(x/n) = 2C₁(log x − c₀)^{1/2} + O(log log x (log x)^{−1/2})`.
-/
import RamanujanTau.SelbergDelange3.Selberg

#print axioms RamanujanTau.SelbergDelange3.mertens_vR_err
#print axioms RamanujanTau.SelbergDelange3.mertens_LamR_err
#print axioms RamanujanTau.SelbergDelange3.recF_log
#print axioms RamanujanTau.SelbergDelange3.abs_recF_le
#print axioms RamanujanTau.SelbergDelange3.logmean_upper_nonneg
#print axioms RamanujanTau.SelbergDelange3.density_nonneg
#print axioms RamanujanTau.SelbergDelange3.fR_prime
#print axioms RamanujanTau.SelbergDelange3.density_fR
#print axioms RamanujanTau.SelbergDelange3.logmean_fR
#print axioms RamanujanTau.SelbergDelange3.rpow_shift_diff
#print axioms RamanujanTau.SelbergDelange3.logmean_LSD_log
#print axioms RamanujanTau.SelbergDelange3.logmean_fR_log
#print axioms RamanujanTau.SelbergDelange3.selberg_sum_fR
