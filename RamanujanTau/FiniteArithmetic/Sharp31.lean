import RamanujanTau.FiniteArithmetic.Divided31
import RamanujanTau.FiniteArithmetic.InitialError31

/-! Exact precision of the contracting error at every even index. -/
set_option autoImplicit false
namespace RamanujanTau.FiniteArithmetic.Sharp31
open PowerSeries BoylanWebb AtkinOBrien AtkinOBrienFinal AllPowers31 Error31 ErrorDynamics31

lemma even_succ (n : ℕ) : Ll 31 (2 * n + 4) = Yop (Ll 31 (2 * n + 2)) := by
  rw [show 2 * n + 4 = 2 * (n + 1) + 2 by omega, even_U, odd_D]
  rfl

lemma U_mem (F : PS 31) (hF : F ∈ B 2) :
    Ulin 31 F ∈ envSub (by norm_num : 5 ≤ 31) 1 (α 31) := by
  refine ⟨?_, U_env (by norm_num) (by norm_num) bounds.1 2 le_rfl _ hF.1.2⟩
  change coeff 0 (U 31 F) = 0
  rw [coeff_U, mul_zero]
  exact hF.1.1

/-- The actual recurrence has normalized errors in a fixed envelope, with
an exact relation between successive errors. -/
theorem normalized_errors : ∃ κ : ℤ_[31], (∃ d : ℤ_[31], κ = 30 + 31 * d) ∧
    ∃ G : ℕ → PS 31, (∀ n, G n ∈ B 2) ∧
      (∀ n, Ll 31 (2 * n + 3) - κ • Ll 31 (2 * n + 1) = (31 : ℤ_[31]) ^ (n + 1) • G n) ∧
      (∀ n, Ll 31 (2 * n + 4) - κ • Ll 31 (2 * n + 2) = (31 : ℤ_[31]) ^ (n + 1) • Ulin 31 (G n)) ∧
      (∀ n, Dlin 31 (Ulin 31 (G n)) = (31 : ℤ_[31]) • G (n + 1)) := by
  obtain ⟨κ, hκ, h⟩ := Divided31.odd_padic_mem
  choose G hmem he using h
  refine ⟨κ, hκ, G, hmem, he, ?_, ?_⟩
  · intro n
    have hh := congrArg (Ulin 31) (he n)
    rw [map_sub, map_smul, map_smul] at hh
    rw [show 2 * n + 4 = 2 * (n + 1) + 2 by omega, even_U, even_U]
    convert hh using 1
  · intro n
    have hh := congrArg Xop (he n)
    rw [map_sub, map_smul, map_smul] at hh
    have hs := he (n + 1)
    have hnext : Ll 31 (2 * (n + 1) + 3) - κ • Ll 31 (2 * (n + 1) + 1) =
        Xop (Ll 31 (2 * n + 3)) - κ • Xop (Ll 31 (2 * n + 1)) := by
      rw [odd_succ, show 2 * (n + 1) + 3 = 2 * (n + 2) + 1 by omega, odd_succ]
      congr 2
    rw [hnext, hh] at hs
    rw [show (31 : ℤ_[31]) ^ (n + 1 + 1) = (31 : ℤ_[31]) ^ (n + 1) * 31 from pow_succ _ _,
      mul_smul] at hs
    apply sub_eq_zero.mp
    apply cancel_pow (31 : ℤ_[31]) PS_reg (n + 1)
    rw [smul_sub]
    change (31 : ℤ_[31]) ^ (n + 1) • Xop (G n) - _ = 0
    rw [hs, sub_self]

/-- Conditional only on the three explicit precision-31² observations.
The scalar certificate prevents the error from disappearing at any iterate. -/
theorem even_exact_of_data (data : Data) : ∃ κ : ℤ_[31], (∃ d : ℤ_[31], κ = 30 + 31 * d) ∧
    ∀ n : ℕ,
      Dvd (31 : ℤ_[31]) (n + 1) (Ll 31 (2 * n + 4) - κ • Ll 31 (2 * n + 2)) ∧
      ¬ Dvd (31 : ℤ_[31]) (n + 2) (Ll 31 (2 * n + 4) - κ • Ll 31 (2 * n + 2)) := by
  obtain ⟨κ, hκ, G, hmem, hodd, heven, hstep⟩ := normalized_errors
  have hobs : ∀ n, PadicInt.toZMod (obs (Ulin 31 (G n))) = 24 * (2 : ZMod 31) ^ n := by
    intro n
    induction n with
    | zero =>
      simpa using InitialError31.initial_observation data κ (Ulin 31 (G 0))
        (by simpa using heven 0)
    | succ n ih =>
      rw [divided_step data _ _ (U_mem _ (hmem n)) (hstep n), ih, pow_succ]
      ring
  refine ⟨κ, hκ, fun n => ⟨⟨_, heven n⟩, ?_⟩⟩
  rintro ⟨V, hV⟩
  rw [show n + 2 = (n + 1) + 1 by omega, pow_succ] at hV
  have hc := congrArg obs ((heven n).symm.trans hV)
  simp only [map_smul, smul_eq_mul, mul_assoc] at hc
  have hcancel := mul_left_cancel₀ (pow_ne_zero (n + 1) (by norm_num : (31 : ℤ_[31]) ≠ 0)) hc
  have hz := congrArg (PadicInt.toZMod (p := 31)) hcancel
  rw [hobs, map_mul, map_ofNat, show (31 : ZMod 31) = 0 from rfl, zero_mul] at hz
  exact (mul_ne_zero (by decide : (24 : ZMod 31) ≠ 0)
    (pow_ne_zero n (by decide : (2 : ZMod 31) ≠ 0))) hz

lemma even_leading_unit (n : ℕ) : IsUnit (coeff 1 (Ll 31 (2 * n + 2))) := by
  have h : PadicInt.toZMod (coeff 1 (Ll 31 (2 * n + 2))) = (10 * 30 ^ n) * (29 : ZMod 31) := by
    rw [← coeff_map, even_U]
    change coeff 1 (PowerSeries.map (PadicInt.toZMod (p := 31)) (U 31 (Ll 31 (2 * n + 1)))) = _
    rw [map_U, odd_reduction, U_C_mul, Cert31.even_step, coeff_C_mul,
      Image31.g_coeff 1 (by decide)]
    rfl
  by_contra hn
  have hz : coeff 1 (Ll 31 (2 * n + 2)) ∈ IsLocalRing.maximalIdeal ℤ_[31] := by
    rw [IsLocalRing.mem_maximalIdeal]
    exact hn
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker, h] at hz
  exact (mul_ne_zero (mul_ne_zero (by decide) (pow_ne_zero n (by decide))) (by decide)) hz

/-- No choice of scalar can move the recurrence one even index earlier. -/
theorem optimal_of_data (data : Data) (n : ℕ) (c : ℤ_[31]) :
    ¬ Dvd (31 : ℤ_[31]) (n + 2) (Ll 31 (2 * n + 4) - c • Ll 31 (2 * n + 2)) := by
  obtain ⟨κ, _, hall⟩ := even_exact_of_data data
  intro hc
  have hnext : Dvd (31 : ℤ_[31]) (n + 2)
      (Ll 31 (2 * (n + 1) + 4) - c • Ll 31 (2 * (n + 1) + 2)) := by
    obtain ⟨V, hV⟩ := hc
    refine ⟨Yop V, ?_⟩
    rw [even_succ (n + 1), show 2 * (n + 1) + 2 = 2 * n + 4 by omega,
      even_succ n]
    rw [even_succ n] at hV
    rw [← map_smul, ← map_sub, hV, map_smul]
  obtain ⟨V, hV⟩ := (hall (n + 1)).1
  obtain ⟨W, hW⟩ := hnext
  have hdiff : (c - κ) • Ll 31 (2 * n + 4) = (31 : ℤ_[31]) ^ (n + 2) • (V - W) := by
    have hi : 2 * (n + 1) + 2 = 2 * n + 4 := by omega
    rw [hi] at hV hW
    rw [smul_sub, ← hV, ← hW, sub_smul]
    abel
  have hcoeff := congrArg (coeff 1) hdiff
  simp only [coeff_smul, smul_eq_mul] at hcoeff
  obtain ⟨u, hu⟩ := even_leading_unit (n + 1)
  have hui : coeff 1 (Ll 31 (2 * n + 4)) * (↑u⁻¹ : ℤ_[31]) = 1 := by
    have hi : 2 * (n + 1) + 2 = 2 * n + 4 := by omega
    rw [hi] at hu
    rw [← hu, Units.mul_inv]
  have hscalar : c - κ = (31 : ℤ_[31]) ^ (n + 2) * (coeff 1 (V - W) * ↑u⁻¹) := by
    calc c - κ = (c - κ) * (coeff 1 (Ll 31 (2 * n + 4)) * ↑u⁻¹) := by rw [hui, mul_one]
      _ = _ := by rw [← mul_assoc, hcoeff, mul_assoc]
  have hd : Dvd (31 : ℤ_[31]) (n + 2) ((c - κ) • Ll 31 (2 * n + 2)) := by
    refine ⟨(coeff 1 (V - W) * ↑u⁻¹) • Ll 31 (2 * n + 2), ?_⟩
    rw [hscalar, mul_smul]
  apply (hall n).2
  convert Dvd_add hc hd using 1
  rw [sub_smul]
  abel

lemma zero_index_fails (c : ℤ_[31]) :
    ¬ Dvd (31 : ℤ_[31]) 1 (Ll 31 2 - c • Ll 31 0) := by
  rintro ⟨V, hV⟩
  have hh := congrArg (fun F => coeff 1 (PowerSeries.map (PadicInt.toZMod (p := 31)) F)) hV
  dsimp only at hh
  rw [map_sub, InitialError31.L2_reduce, map_sub, coeff_smul,
    Image31.g_coeff 1 (by decide)] at hh
  have h0 : Ll 31 0 = 1 := by simp [Ll, L]
  rw [h0, pow_one] at hh
  simp only [PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C,
    map_one, mul_one, coeff_C, coeff_C_mul, map_ofNat, ErrorDynamics31.thirtyOne_series,
    zero_mul, map_zero] at hh
  norm_num at hh
  exact (by decide : (290 : ZMod 31) ≠ 0) hh

/-- The exact starting threshold, at every positive precision. -/
theorem threshold_of_data (data : Data) (m B₀ : ℕ) (hm : 1 ≤ m) :
    (∃ c : ℤ_[31], ∀ b : ℕ, B₀ ≤ b →
      Dvd (31 : ℤ_[31]) m (Ll 31 (b + 2) - c • Ll 31 b)) ↔ 2 * m - 1 ≤ B₀ := by
  constructor
  · rintro ⟨c, hc⟩
    by_contra h
    by_cases hm1 : m = 1
    · subst m
      have hB : B₀ = 0 := by omega
      exact zero_index_fails c (hc 0 (by omega))
    · obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
      exact optimal_of_data data n c (by simpa using hc (2 * n + 2) (by omega))
  · intro hB
    obtain ⟨κ, _, hκ⟩ := series_padic
    refine ⟨κ, fun b hb => Dvd_mono (by omega) (hκ b (by omega))⟩

end RamanujanTau.FiniteArithmetic.Sharp31
