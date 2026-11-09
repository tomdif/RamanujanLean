/-
# Ramanujan's forty identities: definitions and Entry 3.1

`G(q) = Σ_{n≥0} q^{n²}/(q;q)_n` and `H(q) = Σ_{n≥0} q^{n²+n}/(q;q)_n` are defined by their SUM sides
(`tsumQsq`, `tsumQsqQ`), and the Rogers–Ramanujan identities (`rogers_ramanujan_1/2`) give the product forms
`G = 1/((q;q⁵)(q⁴;q⁵))`, `H = 1/((q²;q⁵)(q³;q⁵))` (`G_eq`, `H_eq`).

* `S a f = f(q^a)` (the ring hom `q ↦ q^a`), `Ng f = f(−q)`.
* `fm a = f(−q^a) = (q^a;q^a)_∞`, `chim a = χ(−q^a) = (q^a;q^{2a})_∞`,
  `chip a = χ(q^a) = (−q^a;q^{2a})_∞` (defined as `S a (Ng (q;q²)_∞)`).

**Entry 3.1** (`entry_3_1`): `G¹¹H − q²GH¹¹ = 1 + 11 q G⁶H⁶`, from Ramanujan's `R⁵` identity (`ramanujan_R5`).
-/
import RamanujanTau.RogersRamanujan
import RamanujanTau.RamanujanR5

set_option autoImplicit false

namespace Forty
open PowerSeries Finset
open RankProof (Pinf Ea Ea_Pinf isUnit_Pinf Pinf_aa Pinf_one_one)

/-- `G(q) = Σ_{n≥0} q^{n²}/(q;q)_n`. -/
noncomputable def G : PowerSeries ℤ := MockTheta5.JTP.tsumQsq (fun n => Ring.inverse (MockTheta5.Bailey.qfac n))

/-- `H(q) = Σ_{n≥0} q^{n²+n}/(q;q)_n`. -/
noncomputable def H : PowerSeries ℤ := MockTheta5.JTP.tsumQsqQ (fun n => Ring.inverse (MockTheta5.Bailey.qfac n))

/-- `f ↦ f(q^a)`. -/
noncomputable def S (a : ℕ) [NeZero a] : PowerSeries ℤ →+* PowerSeries ℤ := Ea a (NeZero.ne a)

/-- `f ↦ f(−q)`. -/
noncomputable def Ng : PowerSeries ℤ →+* PowerSeries ℤ := rescale (-1)

/-- `f(−q^a) = (q^a;q^a)_∞`. -/
noncomputable def fm (a : ℕ) : PowerSeries ℤ := Pinf a a

/-- `χ(−q^a) = (q^a;q^{2a})_∞`. -/
noncomputable def chim (a : ℕ) : PowerSeries ℤ := Pinf a (2 * a)

/-- `χ(q^a) = (−q^a;q^{2a})_∞`. -/
noncomputable def chip (a : ℕ) [NeZero a] : PowerSeries ℤ := S a (Ng (Pinf 1 2))

/-- `u = (q;q⁵)_∞(q⁴;q⁵)_∞`, `v = (q²;q⁵)_∞(q³;q⁵)_∞`. -/
noncomputable def uu : PowerSeries ℤ := Pinf 1 5 * Pinf 4 5
noncomputable def vv : PowerSeries ℤ := Pinf 2 5 * Pinf 3 5

lemma isUnit_uu : IsUnit uu := (isUnit_Pinf 1 5 le_rfl (by norm_num)).mul (isUnit_Pinf 4 5 (by norm_num) (by norm_num))
lemma isUnit_vv : IsUnit vv := (isUnit_Pinf 2 5 (by norm_num) (by norm_num)).mul (isUnit_Pinf 3 5 (by norm_num) (by norm_num))

/-- the first Rogers–Ramanujan identity, `G = 1/u`. -/
theorem G_eq : G = Ring.inverse uu := MockTheta5.JTP.RR.rogers_ramanujan_1

/-- the second Rogers–Ramanujan identity, `H = 1/v`. -/
theorem H_eq : H = Ring.inverse vv := MockTheta5.JTP.RR.rogers_ramanujan_2

lemma G_mul_uu : G * uu = 1 := by rw [G_eq, Ring.inverse_mul_cancel _ isUnit_uu]
lemma H_mul_vv : H * vv = 1 := by rw [H_eq, Ring.inverse_mul_cancel _ isUnit_vv]

lemma S_Pinf (a : ℕ) [NeZero a] (b M : ℕ) (hb : 1 ≤ b) (hM : 1 ≤ M) : S a (Pinf b M) = Pinf (a * b) (a * M) :=
  Ea_Pinf a b M (NeZero.ne a) hb hM

/-- `G(q^a) (q^a;q^{5a})(q^{4a};q^{5a}) = 1`. -/
lemma SG_mul (a : ℕ) [NeZero a] : S a G * (Pinf a (5 * a) * Pinf (4 * a) (5 * a)) = 1 := by
  have h := congrArg (S a) G_mul_uu
  rwa [map_mul, map_one, uu, map_mul, S_Pinf a 1 5 le_rfl (by norm_num), S_Pinf a 4 5 (by norm_num) (by norm_num),
    mul_one, mul_comm a 5, mul_comm a 4] at h

/-- `H(q^a) (q^{2a};q^{5a})(q^{3a};q^{5a}) = 1`. -/
lemma SH_mul (a : ℕ) [NeZero a] : S a H * (Pinf (2 * a) (5 * a) * Pinf (3 * a) (5 * a)) = 1 := by
  have h := congrArg (S a) H_mul_vv
  rwa [map_mul, map_one, vv, map_mul, S_Pinf a 2 5 (by norm_num) (by norm_num),
    S_Pinf a 3 5 (by norm_num) (by norm_num), mul_comm a 5, mul_comm a 2, mul_comm a 3] at h

/-- **Entry 3.1** (Rogers 1921, Darling 1921): `G(q)¹¹H(q) − q²G(q)H(q)¹¹ = 1 + 11qG(q)⁶H(q)⁶`. -/
theorem entry_3_1 : G ^ 11 * H - X ^ 2 * G * H ^ 11 = 1 + 11 * X * G ^ 6 * H ^ 6 := by
  have hR := MockTheta5.JTP.ramanujan_R5
  have he : MockTheta5.JTP.eQ = Pinf 5 5 := by
    rw [MockTheta5.JTP.eQ, ← Pinf_one_one, Pinf_aa 5 (by norm_num), ← Pinf_one_one]; rfl
  have hs := MockTheta5.JTP.RR.Pinf_split5
  rw [Pinf_one_one] at hs
  simp only [prod_range_succ, prod_range_zero, one_mul] at hs
  norm_num at hs
  rw [he, hs] at hR
  -- `hR : e⁶ (v¹⁰ − 11 q u⁵v⁵ − q²u¹⁰) = (u v e)⁶ u⁵ v⁵`
  have hG := G_mul_uu
  have hH := H_mul_vv
  have hE : IsUnit (Pinf 5 5) := isUnit_Pinf 5 5 (by norm_num) (by norm_num)
  have key : vv ^ 10 - 11 * X * uu ^ 5 * vv ^ 5 - X ^ 2 * uu ^ 10 = uu ^ 11 * vv ^ 11 := by
    apply (hE.pow 6).mul_left_cancel
    simp only [uu, vv]
    linear_combination hR
  apply ((isUnit_uu.pow 11).mul (isUnit_vv.pow 11)).mul_left_cancel
  calc uu ^ 11 * vv ^ 11 * (G ^ 11 * H - X ^ 2 * G * H ^ 11)
      = (G * uu) ^ 11 * (H * vv) * vv ^ 10 - X ^ 2 * (G * uu) * (H * vv) ^ 11 * uu ^ 10 := by ring
    _ = vv ^ 10 - X ^ 2 * uu ^ 10 := by rw [hG, hH]; ring
    _ = uu ^ 11 * vv ^ 11 + 11 * X * (G * uu) ^ 6 * (H * vv) ^ 6 * uu ^ 5 * vv ^ 5 := by
      rw [hG, hH]; linear_combination key
    _ = uu ^ 11 * vv ^ 11 * (1 + 11 * X * G ^ 6 * H ^ 6) := by ring

end Forty
