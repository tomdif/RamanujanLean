/-
# `SvStripA` step 1b: holomorphy in `z` (`s = 1 − iz`) and the holomorphic `𝒮(z)` (unconditional)

On `Ω = {z : Im z > −1}` (i.e. `Re s > 0`), `x_p(z) = p^{−(1−iz)}` is entire with `‖x_p‖ < 1`,
so every closed-form object is holomorphic in `z`:

* `diff_rhoCF`: `z ↦ ρ(m, 1 − iz)` (`rhoCF`);
* `diff_WdC`, `diff_UdC`, `diff_KqC`: the Cholesky data `W(d)`, `U(h,d)` and the kernel `K^{[s]}`;
* `SvC y z = Σ κ (P₁d/c)^{iz} ρ(P₁,1−iz) ρ(Q₁,1−iz)`: `SvC_ofReal : SvC y v = Sv y v` for real `v`
  (`rhoC = rhoCF` on `Re s = 1`), `diff_SvC : DifferentiableOn ℂ (SvC y) Ω`.

Hence (**`svStripHyp_of_bound`**) `SKQFProof.SvStripHyp c'` reduces to the pure size bound
`SvCBound c'` on the explicit function `SvC` over the strip (no holomorphy/continuation left).
Level 1.
-/
import RamanujanTau.SvStripA.Decomp
import RamanujanTau.SKQFProof.Bound

set_option autoImplicit false

namespace RamanujanTau.SvStripA

open Complex Finset
open RamanujanTau.HafnerBridge (lam)
open RamanujanTau.SelbergKey (Sv sum4 kap P1 Q1 ev rhoC)
open RamanujanTau.SKQFProof (stripR SvStripHyp)

/-- The half-plane `Im z > −1` (`Re (1 − iz) > 0`). -/
def Ω : Set ℂ := {z | -1 < z.im}

lemma isOpen_Ω : IsOpen Ω := isOpen_lt continuous_const Complex.continuous_im

lemma re_s (z : ℂ) : (1 - z * I).re = 1 + z.im := by simp

lemma re_s_pos {z : ℂ} (hz : z ∈ Ω) : 0 < (1 - z * I).re := by
  rw [re_s]; have : -1 < z.im := hz; linarith

lemma diff_xs (p : ℕ) (z : ℂ) (hp : p ≠ 0) : DifferentiableAt ℂ (fun z => xs p (1 - z * I)) z :=
  DifferentiableAt.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hp))

lemma diff_rrK {g : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℂ g z) (h1 : 1 + g z ≠ 0) (μ : ℕ → ℂ)
    (a : ℕ) : DifferentiableAt ℂ (fun z => rrK (g z) μ a) z := by
  unfold rrK
  split_ifs
  · exact differentiableAt_const _
  · exact DifferentiableAt.div (by fun_prop) (by fun_prop) h1

lemma diff_WcK {g : ℂ → ℂ} {z : ℂ} (hg : DifferentiableAt ℂ g z) (h1 : 1 + g z ≠ 0) (l : ℂ)
    (e : ℕ) : DifferentiableAt ℂ (fun z => WcK l (g z) e) z := by
  match e with
  | 0 => exact differentiableAt_const _
  | 1 =>
    simp only [WcK, qqK]
    exact DifferentiableAt.div (by fun_prop) (by fun_prop) (pow_ne_zero 2 h1)
  | (e + 2) =>
    simp only [WcK, qqK]
    exact DifferentiableAt.mul (by fun_prop) (DifferentiableAt.div (by fun_prop) (by fun_prop) h1)

lemma one_add_xs_z {p : ℕ} (hp : p.Prime) {z : ℂ} (hz : z ∈ Ω) : 1 + xs p (1 - z * I) ≠ 0 :=
  one_add_xs_ne hp (re_s_pos hz)

lemma diff_rhoPx {p : ℕ} (hp : p.Prime) (a : ℕ) {z : ℂ} (hz : z ∈ Ω) :
    DifferentiableAt ℂ (fun z => rhoPx p a (xs p (1 - z * I))) z :=
  diff_rrK (diff_xs p z hp.ne_zero) (one_add_xs_z hp hz) (muC p) a

/-- **`z ↦ ρ(m, 1 − iz)` is holomorphic on `Im z > −1`.** -/
theorem diff_rhoCF (m : ℕ) {z : ℂ} (hz : z ∈ Ω) :
    DifferentiableAt ℂ (fun z => rhoCF m (1 - z * I)) z := by
  unfold rhoCF
  exact DifferentiableAt.fun_finsetProd fun p hp =>
    diff_rhoPx (Nat.prime_of_mem_primeFactors hp) _ hz

theorem diff_WdC (d : ℕ) {z : ℂ} (hz : z ∈ Ω) : DifferentiableAt ℂ (fun z => WdC (1 - z * I) d) z := by
  unfold WdC
  exact DifferentiableAt.fun_finsetProd fun p hp =>
    diff_WcK (diff_xs p z (Nat.prime_of_mem_primeFactors hp).ne_zero)
      (one_add_xs_z (Nat.prime_of_mem_primeFactors hp) hz) _ _

lemma diff_LcC {p : ℕ} (hp : p.Prime) (a e : ℕ) {z : ℂ} (hz : z ∈ Ω) :
    DifferentiableAt ℂ (fun z => LcC (1 - z * I) p a e) z := by
  unfold LcC
  split_ifs
  · exact differentiableAt_const _
  · exact (diff_xs p z hp.ne_zero).pow a |>.mul (diff_rhoPx hp a hz)
  · exact ((diff_xs p z hp.ne_zero).pow _).mul (differentiableAt_const _)

theorem diff_UdC (h d : ℕ) {z : ℂ} (hz : z ∈ Ω) : DifferentiableAt ℂ (fun z => UdC (1 - z * I) h d) z := by
  unfold UdC
  split_ifs
  · exact DifferentiableAt.fun_finsetProd fun p hp => diff_LcC (Nat.prime_of_mem_primeFactors hp) _ _ hz
  · exact differentiableAt_const _

theorem diff_KqC {h k : ℕ} (hh : 0 < h) (hk : 0 < k) {z : ℂ} (hz : z ∈ Ω) :
    DifferentiableAt ℂ (fun z => KqC (1 - z * I) h k) z := by
  unfold KqC
  refine ((DifferentiableAt.const_cpow (by fun_prop) (Or.inl ?_)).mul (diff_rhoCF _ hz)).mul
    (diff_rhoCF _ hz)
  exact_mod_cast Nat.lcm_ne_zero hh.ne' hk.ne'

/-! ### The holomorphic `𝒮(z)` -/

/-- `e_z(a,b,c,d) = (P₁ d/c)^{iz}`. -/
noncomputable def evz (a b c d : ℕ) (z : ℂ) : ℂ :=
  cexp (z * I * ((Real.log (P1 a b c d) + Real.log d - Real.log c : ℝ) : ℂ))

/-- `𝒮(z) = Σ κ e_z ρ(P₁, 1−iz) ρ(Q₁, 1−iz)` with closed-form `ρ`. -/
noncomputable def SvC (y : ℕ) (z : ℂ) : ℂ :=
  sum4 y fun a b c d => (kap y a b c d : ℂ) * evz a b c d z *
    rhoCF (P1 a b c d) (1 - z * I) * rhoCF (Q1 a b c d) (1 - z * I)

/-- **`SvC` extends `Sv`**: `SvC y v = Sv y v` for real `v`. -/
theorem SvC_ofReal (y : ℕ) (v : ℝ) : SvC y v = Sv y v := by
  have hs : (11 / 20 : ℝ) < (1 - (v : ℂ) * I).re := by rw [re_s]; simp; norm_num
  unfold SvC Sv sum4
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ =>
    sum_congr rfl fun d _ => ?_
  simp only
  rw [rhoC_eq_rhoCF _ hs, rhoC_eq_rhoCF _ hs]
  rfl

/-- **`SvC y` is holomorphic on `Im z > −1`.** -/
theorem diff_SvC (y : ℕ) : DifferentiableOn ℂ (SvC y) Ω := by
  intro z hz
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold SvC sum4
  refine DifferentiableAt.fun_sum fun a _ => DifferentiableAt.fun_sum fun b _ =>
    DifferentiableAt.fun_sum fun c _ => DifferentiableAt.fun_sum fun d _ => ?_
  refine (((differentiableAt_const _).mul ?_).mul (diff_rhoCF _ hz)).mul (diff_rhoCF _ hz)
  unfold evz
  fun_prop

lemma stripR_sub_Ω {δ₀ : ℝ} (hδ : δ₀ < 1) : stripR δ₀ ⊆ Ω := by
  intro z hz
  have : -δ₀ ≤ z.im := hz.2.1
  show -1 < z.im
  linarith

/-- The remaining size bound on the explicit holomorphic `SvC` (all continuation is done). -/
def SvCBound (c' : ℝ) : Prop :=
  ∃ C δ₀ : ℝ, 0 ≤ C ∧ 0 < δ₀ ∧ δ₀ < 1 ∧ ∀ y : ℕ, 2 ≤ y → ∀ z ∈ stripR δ₀, ‖SvC y z‖ ≤
    C * (1 + |z.re| * Real.log y) ^ 2 * Real.exp (c' * |z.im| * Real.log y) / Real.log y

/-- **`SvStripHyp c'` reduces to the size bound `SvCBound c'`** (holomorphic continuation proved). -/
theorem svStripHyp_of_bound {c' : ℝ} (H : SvCBound c') : SvStripHyp c' := by
  obtain ⟨C, δ₀, hC, hδ, hδ1, hB⟩ := H
  refine ⟨C, δ₀, hC, hδ, fun y hy => ⟨SvC y, Ω, isOpen_Ω, stripR_sub_Ω hδ1, diff_SvC y,
    fun v _ => SvC_ofReal y v, hB y hy⟩⟩

end RamanujanTau.SvStripA
