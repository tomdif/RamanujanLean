/-
# `SvStripC` (S2 of `docs/SKQF_PROOF.md` §4): definitions of the twisted factorization data

**Stable interface** (imported by `SvStripD`; do not rename).  `s = 1 − iz`, `tw z m = m^{iz}`.

* `Fiz z m = Fi(m) m^{iz}`: the Dirichlet inverse of `Fz z m = F(m) m^{iz}`, `F = fR/n` (`Fm`);
  `J_z(x) = Σ_{m≤x} Fz z m log(x/m)` (`SvStripB.Jz`).
* `Gz z d v₁ v₂ = v₂^{−iz} U^{[s]}(v₁v₂, d)` (`U^{[s]} = SvStripA.UdC s`): the summand of `y_d`.
* **`Γz z d u₁ u₂ = Σ_{v₁|u₁, v₂|u₂} α(v₁)α(v₂) Gz z d v₁ v₂ Fiz z (u₁/v₁) Fi(u₂/v₂)`**
  (the canonical twisted `Γ`; twisted `Fi` on the `J_z` side, plain `Fi` on the `J_0` side).
* `γz z p e i j`: its local factor (`Prod.lean`: `Γz = Π_p γz z p (v_p d)(v_p u₁)(v_p u₂)`),

      γz z p e i j = Σ_{a≤i, b≤j} α(p^a)α(p^b) (p^{−iz})^b L_p^{[s]}(a+b, e)
                       · Fi(p^{i−a}) (p^{iz})^{i−a} · Fi(p^{j−b}),

  with `L_p^{[s]} = SvStripA.LcC s p` (`L(a,0) = x^a ρ_p(a,x)`, `L(a,e) = x^{a−e}λ(p^{a−e})`, `x = p^{−s}`).
* `xz y z P = Σ_{ac=P, a,c≤y} β(a)β(c) c^{−iz}`; `SvBil y z = Σ_{P,Q≤y²} xz(P) xz(Q) K^{[s]}(P,Q)`.
* `Yd y z d = Σ_{n₁,n₂≤y} β(n₁)β(n₂) Gz z d n₁ n₂` (`= Σ_P xz(P) U^{[s]}(P,d)`);
  `YdJ y z d = (log y)^{−2} Σ_{u₁,u₂≤y} Γz z d u₁ u₂ J_z(y/u₁) J_0(y/u₂)` — exactly the expression
  bounded by `SvStripB.yd_bound_div` with `Γ = Γz z d`.

Main identities (`Ident.lean`): `SvC y z = SvBil y z` (all `z`), `SvBil y z = Σ_{d≤y²} W^{[s]}(d) Yd²`
(`Im z > −1`), `Yd = YdJ` (`y ≥ 2`).
-/
import RamanujanTau.SvStripA.Holo
import RamanujanTau.SvStripB.JTwist
import RamanujanTau.QFProof3.Factor

set_option autoImplicit false

namespace RamanujanTau.SvStripC

open Complex Finset
open RamanujanTau.SvStripA (UdC LcC WdC KqC SvC)
open RamanujanTau.SvStripB (Jz)
open RamanujanTau.QFProof (Fm)
open RamanujanTau.QFProof3 (Fi)
open RamanujanTau.SelbergCoeffs (alpha)
open RamanujanTau.HafnerMV2 (βSel)

/-- The twist `m^{iz}`. -/
noncomputable def tw (z : ℂ) (m : ℕ) : ℂ := (m : ℂ) ^ (I * z)

/-- `F_z(m) = (fR(m)/m) m^{iz}`. -/
noncomputable def Fz (z : ℂ) (m : ℕ) : ℂ := (Fm m : ℂ) * tw z m

/-- The twisted `Fi`: `Fi_z(m) = Fi(m) m^{iz}` (Dirichlet inverse of `F_z`). -/
noncomputable def Fiz (z : ℂ) (m : ℕ) : ℂ := (Fi m : ℂ) * tw z m

/-- `G^z_d(v₁,v₂) = v₂^{−iz} U^{[1−iz]}(v₁v₂, d)`. -/
noncomputable def Gz (z : ℂ) (d v₁ v₂ : ℕ) : ℂ := tw (-z) v₂ * UdC (1 - z * I) (v₁ * v₂) d

/-- **The twisted factor kernel `Γ^z_d(u₁,u₂)`.** -/
noncomputable def Γz (z : ℂ) (d u₁ u₂ : ℕ) : ℂ :=
  ∑ v₁ ∈ u₁.divisors, ∑ v₂ ∈ u₂.divisors,
    ((alpha v₁ * alpha v₂ : ℝ) : ℂ) * Gz z d v₁ v₂ * Fiz z (u₁ / v₁) * (Fi (u₂ / v₂) : ℂ)

/-- The local factor of `Γz` at `p` (`e = v_p d`, `i = v_p u₁`, `j = v_p u₂`). -/
noncomputable def γz (z : ℂ) (p e i j : ℕ) : ℂ :=
  ∑ a ∈ Icc 0 i, ∑ b ∈ Icc 0 j,
    ((alpha (p ^ a) * alpha (p ^ b) : ℝ) : ℂ) * tw (-z) p ^ b * LcC (1 - z * I) p (a + b) e *
      ((Fi (p ^ (i - a)) : ℂ) * tw z p ^ (i - a)) * (Fi (p ^ (j - b)) : ℂ)

/-- `x_z(P) = Σ_{ac=P, a,c≤y} β(a)β(c) c^{−iz}`. -/
noncomputable def xz (y : ℕ) (z : ℂ) (P : ℕ) : ℂ :=
  ∑ a ∈ Icc 1 y, ∑ c ∈ Icc 1 y,
    if a * c = P then ((βSel y a * βSel y c : ℝ) : ℂ) * tw (-z) c else 0

/-- The bilinear form `Σ_{P,Q≤y²} x_z(P) x_z(Q) K^{[1−iz]}(P,Q)`. -/
noncomputable def SvBil (y : ℕ) (z : ℂ) : ℂ :=
  ∑ P ∈ Icc 1 (y ^ 2), ∑ Q ∈ Icc 1 (y ^ 2), xz y z P * xz y z Q * KqC (1 - z * I) P Q

/-- `y_d(z) = Σ_{n₁,n₂≤y} β(n₁)β(n₂) n₂^{−iz} U^{[s]}(n₁n₂, d)`. -/
noncomputable def Yd (y : ℕ) (z : ℂ) (d : ℕ) : ℂ :=
  ∑ n₁ ∈ Icc 1 y, ∑ n₂ ∈ Icc 1 y, ((βSel y n₁ * βSel y n₂ : ℝ) : ℂ) * Gz z d n₁ n₂

/-- `y_d(z)` in smoothed form: `(log y)^{−2} Σ_{u₁,u₂≤y} Γ^z_d(u₁,u₂) J_z(y/u₁) J_0(y/u₂)`. -/
noncomputable def YdJ (y : ℕ) (z : ℂ) (d : ℕ) : ℂ :=
  (∑ u₁ ∈ Ioc 0 y, ∑ u₂ ∈ Ioc 0 y, Γz z d u₁ u₂ * Jz z ((y : ℝ) / u₁) * Jz 0 ((y : ℝ) / u₂)) /
    (Real.log y : ℂ) ^ 2

end RamanujanTau.SvStripC
