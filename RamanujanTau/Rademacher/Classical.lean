/-
# Rademacher's formula, classical form

`p(n) = Σ_{k≥1} A_k(n) · (π/12k)^{3/2} · 2π · 4(u_k cosh u_k − sinh u_k)/(√π u_k³) / k`, `u_k = (π/k)√(2(n−1/24)/3)`,

with Rademacher's Kloosterman sum `A_k(n) = Σ_{0≤h<k, (h,k)=1} e^{πi s(h,k) − 2πinh/k}`, `s(h,k)` the Dedekind sum.
-/
import RamanujanTau.Rademacher.Closed
import RamanujanTau.Rademacher.DedekindOmega

set_option autoImplicit false

namespace Rademacher
open Complex Filter
open scoped Real Topology

noncomputable section

/-- **Rademacher's convergent series for `p(n)`**, with the multiplier written as `e^{πi s(h,k)}`. -/
theorem rademacher_dedekind (n : ℕ) (hn : 1 ≤ n) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
        (∑ h ∈ (Finset.range k).filter (fun h => Nat.Coprime h k),
          cexp (π * I * dsum h k - 2 * π * I * n * h / k)) * (radTerm k n : ℂ))
      atTop (𝓝 (HardyRamanujan.p n : ℂ)) := by
  refine (rademacher n hn).congr fun N => Finset.sum_congr rfl fun k hk => ?_
  rw [Ak_eq_dedekind k n (by have := (Finset.mem_Icc.mp hk).1; omega)]

end

end Rademacher
