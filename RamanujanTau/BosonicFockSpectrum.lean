import RamanujanTau.BosonicHilbert

/-!
# Finite energy eigenspaces inside the completed occupation space

An eigenvector of the maximal Hamiltonian is supported at its exact energy.
Each natural-energy eigenspace is isometrically equivalent to the earlier
finite normalized shell. Completion therefore preserves the partition-count
degeneracies and the proved leading entropy. This is a statement about
eigenspaces, not a calculation of the operator's full resolvent spectrum.
-/

set_option autoImplicit false
noncomputable section

namespace BosonicOscillator

open Filter
open scoped Classical Real Topology

def FockEnergySpace (k n : ℕ) : Submodule ℂ (FockSpace k) where
  carrier := {x | ∀ d, exponentEnergy d ≠ n → x d = 0}
  zero_mem' := by intro d _; rfl
  add_mem' hx hy := by
    intro d hd
    change _ + _ = 0
    rw [hx d hd, hy d hd, add_zero]
  smul_mem' c x hx := by
    intro d hd
    change c * x d = 0
    rw [hx d hd, mul_zero]

def extendShell {k n : ℕ} (v : NormalizedShell k n) : FockSpace k :=
  ⟨fun d => if h : exponentEnergy d = n then v ⟨d, h⟩ else 0, by
    apply Memℓp.of_exponent_ge (p := 0) zero_le
    apply memℓp_zero
    apply ({d : Exponent k | exponentEnergy d = n}.toFinite).subset
    intro d hd
    by_contra h
    exact hd (dif_neg h)⟩

theorem extendShell_apply {k n : ℕ} (v : NormalizedShell k n) (d : Exponent k) :
    extendShell v d = if h : exponentEnergy d = n then v ⟨d, h⟩ else 0 := rfl

def fockShellEquiv (k n : ℕ) : FockEnergySpace k n ≃ₗ[ℂ] NormalizedShell k n where
  toFun x := WithLp.toLp 2 (fun d => x.1 d.1)
  invFun v := ⟨extendShell v, by intro d hd; exact dif_neg hd⟩
  left_inv x := by
    apply Subtype.ext
    ext d
    by_cases h : exponentEnergy d = n
    · simp [extendShell_apply, h]
    · simp [extendShell_apply, h, x.2 d h]
  right_inv v := by
    ext d
    simp [extendShell_apply, d.2]
  map_add' := by intro x y; ext d; rfl
  map_smul' := by intro c x; ext d; rfl

@[simp] theorem fockShellEquiv_apply {k n : ℕ} (x : FockEnergySpace k n) (d : EnergyIndex k n) :
    fockShellEquiv k n x d = x.1 d.1 := rfl

theorem fockShellEquiv_inner {k n : ℕ} (x y : FockEnergySpace k n) :
    inner ℂ (fockShellEquiv k n x) (fockShellEquiv k n y) = inner ℂ x y := by
  rw [PiLp.inner_apply]
  change (∑ d : EnergyIndex k n, inner ℂ (x.1 d.1) (y.1 d.1)) = inner ℂ x.1 y.1
  rw [lp.inner_eq_tsum, ← tsum_fintype]
  apply tsum_subtype_eq_of_support_subset
  intro d hd
  change exponentEnergy d = n
  by_contra h
  exact hd (by simp [x.2 d h])

def fockShellIsometry (k n : ℕ) : FockEnergySpace k n ≃ₗᵢ[ℂ] NormalizedShell k n :=
  (fockShellEquiv k n).isometryOfInner fockShellEquiv_inner

instance (k n : ℕ) : FiniteDimensional ℂ (FockEnergySpace k n) :=
  FiniteDimensional.of_injective (fockShellEquiv k n).toLinearMap
    (fockShellEquiv k n).injective

theorem fockEnergySpace_finrank (k n : ℕ) :
    Module.finrank ℂ (FockEnergySpace k n) = ColoredPartitions.count k n := by
  rw [(fockShellEquiv k n).finrank_eq, normalizedShell_finrank]

/-- The support condition is exactly the eigenvector equation, including domain membership. -/
theorem mem_fockEnergySpace_iff {k n : ℕ} (x : FockSpace k) :
    x ∈ FockEnergySpace k n ↔
      ∃ hx : x ∈ (fockHamiltonian k).domain, fockHamiltonian k ⟨x, hx⟩ = (n : ℂ) • x := by
  constructor
  · intro hx
    have hf : (fun d => (exponentEnergy d : ℂ) * x d) = fun d => (n : ℂ) * x d := by
      funext d
      by_cases h : exponentEnergy d = n
      · rw [h]
      · rw [hx d h, mul_zero, mul_zero]
    have hd : x ∈ (fockHamiltonian k).domain := by
      change Memℓp (fun d => ((exponentEnergy d : ℝ) : ℂ) * x d) 2
      simp only [Complex.ofReal_natCast]
      rw [hf]
      exact (lp.memℓp x).const_smul (n : ℂ)
    refine ⟨hd, ?_⟩
    ext d
    rw [fockHamiltonian_apply]
    exact congrFun hf d
  · rintro ⟨hx, h⟩ d hd
    have hc := congrArg (fun y : FockSpace k => y d) h
    rw [fockHamiltonian_apply] at hc
    change (exponentEnergy d : ℂ) * x d = (n : ℂ) * x d at hc
    by_contra hne
    have he := mul_right_cancel₀ hne hc
    exact hd (by exact_mod_cast he)

theorem fockCharge_domain_eq : fockCharge.domain = (fockHamiltonian 24).domain := by
  ext x
  change Memℓp (fun d => (((exponentEnergy d : ℝ) - 1 : ℝ) : ℂ) * x d) 2 ↔
    Memℓp (fun d => ((exponentEnergy d : ℝ) : ℂ) * x d) 2
  simp only [Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_one]
  constructor
  · intro hx
    have h := hx.add (lp.memℓp x)
    convert h using 1
    funext d
    change (exponentEnergy d : ℂ) * x d = ((exponentEnergy d : ℂ) - 1) * x d + x d
    ring
  · intro hx
    have h := hx.sub (lp.memℓp x)
    convert h using 1
    funext d
    change ((exponentEnergy d : ℂ) - 1) * x d = (exponentEnergy d : ℂ) * x d - x d
    ring

theorem fockCharge_eq_hamiltonian_sub (x : fockCharge.domain) :
    fockCharge x = fockHamiltonian 24 ⟨x.1, fockCharge_domain_eq ▸ x.2⟩ - x.1 := by
  ext d
  rw [fockCharge_apply]
  change ((exponentEnergy d : ℂ) - 1) * x.1 d =
    fockHamiltonian 24 ⟨x.1, fockCharge_domain_eq ▸ x.2⟩ d - x.1 d
  rw [fockHamiltonian_apply]
  ring

abbrev FockChargeSpace (n : ℕ) := FockEnergySpace 24 (n + 1)

theorem mem_fockChargeSpace_iff (n : ℕ) (x : FockSpace 24) :
    x ∈ FockChargeSpace n ↔
      ∃ hx : x ∈ fockCharge.domain, fockCharge ⟨x, hx⟩ = (n : ℂ) • x := by
  rw [mem_fockEnergySpace_iff]
  constructor
  · rintro ⟨hx, he⟩
    refine ⟨fockCharge_domain_eq.symm ▸ hx, ?_⟩
    rw [fockCharge_eq_hamiltonian_sub]
    change fockHamiltonian 24 ⟨x, hx⟩ - x = (n : ℂ) • x
    rw [he, Nat.cast_add, Nat.cast_one, add_smul, one_smul]
    abel
  · rintro ⟨hx, he⟩
    refine ⟨fockCharge_domain_eq ▸ hx, ?_⟩
    have h := fockCharge_eq_hamiltonian_sub ⟨x, hx⟩
    rw [he] at h
    rw [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
    exact sub_eq_iff_eq_add.mp h.symm

theorem fockChargeSpace_finrank (n : ℕ) :
    Module.finrank ℂ (FockChargeSpace n) = ColoredPartitions.degeneracy n :=
  fockEnergySpace_finrank 24 (n + 1)

theorem fockChargeSpace_entropy :
    Tendsto (fun n : ℕ => Real.log (Module.finrank ℂ (FockChargeSpace n) : ℝ) / √n)
      atTop (𝓝 (4 * π)) := by
  simpa only [fockChargeSpace_finrank] using ColoredPartitions.degeneracy_entropy

theorem fockChargeSpace_cardy_ratio :
    Tendsto (fun n : ℕ => Real.log (Module.finrank ℂ (FockChargeSpace n) : ℝ) /
      Cardy.leadingEntropy 2 n) atTop (𝓝 1) := by
  simpa only [fockChargeSpace_finrank] using ColoredPartitions.degeneracy_cardy_ratio

end BosonicOscillator
