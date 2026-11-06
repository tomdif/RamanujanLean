/-
# Selberg's key lemma: diagonal clause (M3/M4) — entry point

* `Conv`: the lag convolution identity `∫_0^h∫_0^h a(x'−x) = ∫_{−h}^{h}(h−|v|)a(v)` (Fubini);
* `Meas`: measurability of `𝒮`, `𝒮⁰`, `𝒜` in the lag `v`;
* `Generic`: a lag integral from a pointwise approximant (M4 core);
* `Reduce`: `DiagApproxHyp` (M3 output, named), the `L`-shift lemma, `diagLag_bound_of_SKQF`;
* `Assemble`: `diagHypT_of_SKQF`, `sk_of_SKQF`, positive proportion;
* `DiagIndex`: M3 step 1, the diagonal `bdn = acm` is the ray `(Q₁r, P₁r)`.
See `docs/SELBERG_KEY.md` (2026-11-06, diagonal section).
-/
import RamanujanTau.SelbergKeyDiag.Assemble
import RamanujanTau.SelbergKeyDiag.DiagIndex

open RamanujanTau.SelbergKeyDiag

#print axioms lag_conv
#print axioms measurable_Av
#print axioms lagInt_le_of_approx
#print axioms abs_reAv_sub_le
#print axioms diagLag_bound_of_SKQF
#print axioms diagLag_bound_phiT
#print axioms diagHypT_of_SKQF
#print axioms sk_of_SKQF
#print axioms tauL_positive_proportion_of_SKQF
#print axioms diagS_eq_tsum_ray
