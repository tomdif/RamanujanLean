/-
# The exact Jensen thresholds `N(6) = 610` and `N(7) = 908` for the partition function, unconditionally

* `jensen6_tail : JensenTail 6 1259` and `jensen7_tail : JensenTail 7 1676`: the analytic tail. The proof uses
  the Lean-proved Rademacher/Lehmer bound `|p(n) − Mmain n| ≤ Kc e^{U/2}` (`Rademacher.p_sub_main_le`), Taylor
  bounds along the derivative chain of `log Mmain`, the Leibniz chain for `e^φ`, and a kernel-checked
  fixed-point interval certificate over 16 (d = 6) and 25 (d = 7) boxes in `t₀ = U(n)^{-1/2}`. The last box
  `t₀ ∈ [0, ·]` covers all large `n`.
* Combined with the kernel-checked finite ranges (`jensen6_finite`, `jensen7_finite`) and the Laguerre
  failures (`jensen6_fails`, `jensen7_fails`).
-/
import RamanujanTau.JensenThreshold.Tail.Cover
import RamanujanTau.JensenThreshold.Tail.Check6
import RamanujanTau.JensenThreshold.Tail.Check7
import RamanujanTau.JensenThreshold.Jensen6
import RamanujanTau.JensenThreshold.Jensen7

set_option autoImplicit false

namespace JensenThreshold

open Tail Rademacher

/-- a contiguous box list, all boxes certified, covering `t₀ ≤ t_max`, gives the tail from `n₀`. -/
theorem tail_of_boxes {d K N : ℕ} (hNew : NewtonId d) (L : List BoxD) (tm : ℤ × ℤ)
    (hall : L.all (checkBox d K N) = true) (hcov : coverOK L tm = true) (hp : 0 < tm.1) (hq : 0 < tm.2)
    {n₀ : ℕ} (hn0 : 2 ≤ n₀) (hnum : tm.2 ^ 4 * 720000000000 ≤ 2 * 314159 ^ 2 * (24 * (n₀ : ℤ) - 1) * tm.1 ^ 4) :
    JensenTail d n₀ := by
  intro n hn
  have ht := t0_le_tmax hp hq (by omega) hnum hn
  obtain ⟨B, hBmem, h1, h2⟩ := coverOK_spec L tm hcov hq (t0v (uk 1 n)) (t0v_nonneg _) ht
  have hc := (List.all_eq_true.mp hall) B hBmem
  exact box_sound hNew hc (by omega) h1 h2

/-- **The degree-6 tail**: `J^{6,n}` is hyperbolic for every `n ≥ 1259`. -/
theorem jensen6_tail : JensenTail 6 1259 :=
  tail_of_boxes newton6 boxes6 tmax6 boxes6_ok cover6_ok (by decide) (by decide) (by norm_num)
    (by norm_num [tmax6])

/-- **The degree-7 tail**: `J^{7,n}` is hyperbolic for every `n ≥ 1676`. -/
theorem jensen7_tail : JensenTail 7 1676 :=
  tail_of_boxes newton7 boxes7 tmax7 boxes7_ok cover7_ok (by decide) (by decide) (by norm_num)
    (by norm_num [tmax7])

/-- **`N(6) = 610`**: `J^{6,n}(X) = Σ_{j≤6} C(6,j) p(n+j) X^j` has only real roots for every `n ≥ 610`,
and `J^{6,609}` does not. -/
theorem jensen6_threshold_unconditional :
    (∀ n, 610 ≤ n → Hyperbolic (jensen 6 n)) ∧ ¬ Hyperbolic (jensen 6 609) :=
  jensen6_threshold jensen6_tail

/-- **`N(7) = 908`**: `J^{7,n}` has only real roots for every `n ≥ 908`, and `J^{7,907}` does not. -/
theorem jensen7_threshold_unconditional :
    (∀ n, 908 ≤ n → Hyperbolic (jensen 7 n)) ∧ ¬ Hyperbolic (jensen 7 907) :=
  jensen7_threshold jensen7_tail

end JensenThreshold
