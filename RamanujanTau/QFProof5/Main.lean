/-
# `QFProof5/` — the three Euler bounds under `[DeligneBound]`; `QFHyp` and (MV2) under Deligne only

Build: `nice -n 10 lake build RamanujanTau.QFProof5.Main`. See `docs/QF_PROOF.md` (2026-11-06, QFProof5).

* `Local`: local masses L1–L6 (`Tl_zero_le`, `Tl_one_le`, `Tl_le`, `TlV_zero_le`, `TlV_one_le`, `TlV_le`);
* `Euler`: `logmean_geo` (geometric prime-power growth) and `euler_fT` (κ = 1 via `mertens2_bound`);
* `Assemble`: `qEuler1`, `qEuler2`, `qEuler3`;
* **`qfHyp_deligne [DeligneBound] : QFHyp`** and **`mv2_deligne [DeligneBound]`** (Hafner's (MV2) for
  Selberg's mollifier, `0 < θ ≤ 1/81600`).
-/
import RamanujanTau.QFProof5.Assemble
import RamanujanTau.QFProof4.Main

namespace RamanujanTau.QFProof5

open RamanujanTau.QFProof RamanujanTau.QFProof3 Complex
open RamanujanTau.HafnerProportion RamanujanTau.HeckeL RamanujanTau.SelbergCoeffs

/-- **`QFHyp` under Deligne's bound only.** -/
theorem qfHyp_deligne [DeligneBound] : RamanujanTau.HafnerBridge.QFHyp :=
  qfHyp_of_euler qEuler1 qEuler2 qEuler3

/-- **Hafner's (MV2) for Selberg's mollifier under Deligne's bound only.** -/
theorem mv2_deligne [DeligneBound] {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 81600) :
    ∃ B T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      (∫ u in T..(3 * T), ‖tauL (6 + u * I) * Mc (bSel ⌊T ^ θ⌋₊) ⌊T ^ θ⌋₊ (6 + u * I) ^ 2‖ ^ 2) ≤ B * T :=
  RamanujanTau.QFProof4.mv2_of_euler hθ0 hθ qEuler1 qEuler2 qEuler3

end RamanujanTau.QFProof5

#print axioms RamanujanTau.QFProof5.conv1_le
#print axioms RamanujanTau.QFProof5.wmass_le
#print axioms RamanujanTau.QFProof5.Tl_zero_le
#print axioms RamanujanTau.QFProof5.Tl_one_le
#print axioms RamanujanTau.QFProof5.Tl_le
#print axioms RamanujanTau.QFProof5.TlV_zero_le
#print axioms RamanujanTau.QFProof5.TlV_one_le
#print axioms RamanujanTau.QFProof5.TlV_le
#print axioms RamanujanTau.QFProof5.logmean_geo
#print axioms RamanujanTau.QFProof5.euler_fT
#print axioms RamanujanTau.QFProof5.Mass_le_tt
#print axioms RamanujanTau.QFProof5.MassV_le_tt
#print axioms RamanujanTau.QFProof5.qEuler1
#print axioms RamanujanTau.QFProof5.qEuler2
#print axioms RamanujanTau.QFProof5.qEuler3
#print axioms RamanujanTau.QFProof5.qfHyp_deligne
#print axioms RamanujanTau.QFProof5.mv2_deligne
