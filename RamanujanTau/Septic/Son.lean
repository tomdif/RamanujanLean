/-
# Son's Entry 1.1(ii)–(v): what is proved and the one remaining gap

Variable `q` = Rebák's `q^{1/7}`. 7-dissection components of `φ(q)`:

  `a = φ(q⁴⁹)`, `b = q f(q³⁵,q⁶³)`, `c = q⁴ f(q²¹,q⁷⁷)`, `d = q⁹ f(q⁷,q⁹¹)`, `Φ = φ(q⁷)`,

so `u = 2b/a`, `v = 2c/a`, `w = 2d/a`, `p = uvw = 8bcd/a³`, `R = φ⁴(q⁷)/φ⁴(q⁴⁹) = Φ⁴/a⁴` (Rebák's
`φ⁴(q)/φ⁴(q⁷)`).

**Reformulation of (iv)/(v).** Solving `u⁷ = α²p/β, v⁷ = β²p/γ, w⁷ = γ²p/α` gives `α = u³v`, `β = v³w`,
`γ = w³u`. So (iv)+(v) say exactly that `u³v, v³w, w³u` are the roots of
`r(ξ) = ξ³ + 2(1+3p−R)ξ² + p²(p+4)ξ − p⁴`. Since their product is automatically `p⁴`, this is two identities:

* `u³v + v³w + w³u = 2R − 6p − 2`, i.e. `Φ⁴ = a⁴ + 24abcd + 8(b³c + c³d + d³b)`.
  **PROVED** as `quaternion_identity` (`Septic/Quaternion.lean`).
* `u²v³ + v²w³ + w²u³ = p² + 4p`, i.e. `a(b²c³ + c²d³ + d²b³) = a³bcd + 2(bcd)²`. This is `SonSextic`.
  It is a relation among `a, b, c, d` alone; numerically there is none of degree `< 6`.

Entry 1.1(iii) `R² − (2+5p)R + (1−p)³ = 0`, multiplied by `a⁹`, is `SonEntryIII`. Together with
`R = 7` at `q = e^{−π/(7√7)}` (Lemma 2.1), it forces `p = 1`: `(1−p)((1−p)² + 35) = 0`. So it **replaces the
class invariant `G₇ = 2^{1/4}`** in Rebák's proof.

Both are checked exactly as integer power series to `q^600` by `scripts/septic/check_son_core.py`.
That script also checks that (iii) lies in the ideal of the six sextic relations among `a, b, c, d`.
-/
import RamanujanTau.Septic.Quaternion

set_option autoImplicit false

namespace RamanujanTau.Septic

open PowerSeries

/-- **Son's sextic relation** (Entry 1.1(iv)/(v), second elementary symmetric function of
`u³v, v³w, w³u`): `a(b²c³ + c²d³ + d²b³) = a³bcd + 2(bcd)²`, i.e. `u²v³ + v²w³ + w²u³ = p² + 4p`. -/
def SonSextic : Prop :=
  ramF 49 49 * ((X * ramF 35 63) ^ 2 * (X ^ 4 * ramF 21 77) ^ 3
      + (X ^ 4 * ramF 21 77) ^ 2 * (X ^ 9 * ramF 7 91) ^ 3
      + (X ^ 9 * ramF 7 91) ^ 2 * (X * ramF 35 63) ^ 3)
    = ramF 49 49 ^ 3 * (X * ramF 35 63) * (X ^ 4 * ramF 21 77) * (X ^ 9 * ramF 7 91)
      + 2 * ((X * ramF 35 63) * (X ^ 4 * ramF 21 77) * (X ^ 9 * ramF 7 91)) ^ 2

/-- **Entry 1.1(iii)** `R² − (2+5p)R + (1−p)³ = 0` with `R = Φ⁴/a⁴`, `p = 8bcd/a³`, times `a⁹`. -/
def SonEntryIII : Prop :=
  ramF 49 49 * ramF 7 7 ^ 8
      + (ramF 49 49 ^ 3 - 8 * (X * ramF 35 63) * (X ^ 4 * ramF 21 77) * (X ^ 9 * ramF 7 91)) ^ 3
    = (2 * ramF 49 49 ^ 5
        + 40 * ramF 49 49 ^ 2 * (X * ramF 35 63) * (X ^ 4 * ramF 21 77) * (X ^ 9 * ramF 7 91))
      * ramF 7 7 ^ 4

/-- **The single remaining gap** for the page-206 evaluation: Son's sextic relation and Entry 1.1(iii),
as identities in `ℤ⟦q⟧`. `SepticSonCore → Page206Evaluation` is `page206_of_sonCore`. -/
def SepticSonCore : Prop := SonSextic ∧ SonEntryIII

lemma sonSextic_T (h : SonSextic) :
    T 0 * (T 1 ^ 2 * T 2 ^ 3 + T 2 ^ 2 * T 3 ^ 3 + T 3 ^ 2 * T 1 ^ 3)
      = T 0 ^ 3 * T 1 * T 2 * T 3 + 2 * (T 1 * T 2 * T 3) ^ 2 := by
  rw [T0_eq, T1_eq, T2_eq, T3_eq]; exact h

lemma sonEntryIII_T (h : SonEntryIII) :
    T 0 * ramF 7 7 ^ 8 + (T 0 ^ 3 - 8 * T 1 * T 2 * T 3) ^ 3
      = (2 * T 0 ^ 5 + 40 * T 0 ^ 2 * T 1 * T 2 * T 3) * ramF 7 7 ^ 4 := by
  rw [T0_eq, T1_eq, T2_eq, T3_eq]; exact h

/-- Entry 1.1(i) in `T`-form: `φ = a + 2b + 2c + 2d`. -/
lemma phi_T : phi = T 0 + 2 * T 1 + 2 * T 2 + 2 * T 3 := by
  rw [T0_eq, T1_eq, T2_eq, T3_eq, phi_seven_dissection]; ring

end RamanujanTau.Septic
