/-
# Well-definedness of the local factors in `QFHyp`

Unconditionally (via `TauPNTUncond.tau_le_uniform`, `|τ(n)| ≪ n^{231/40}`): `|λ(n)| ≤ C n^{11/40}`, so the
series `D_p`, `N_p(a)`, `D_p'`, `N_p'(a)` converge absolutely (ratio `p^{−9/20}`), and `D_p ≥ 1`.
-/
import RamanujanTau.HafnerBridge.QF
import RamanujanTau.TauPNTUncond.Weil

set_option autoImplicit false

namespace RamanujanTau.HafnerBridge

lemma lam_bound : ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → |lam n| ≤ C * (n : ℝ) ^ (11 / 40 : ℝ) := by
  obtain ⟨C, hC1, hC⟩ := RamanujanTau.TauPNTUncond.tau_le_uniform
  refine ⟨C, hC1, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [lam, RamanujanTau.SubconvexityCond.lam]
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hn0 _)]
  calc |(RamanujanTau.tau n : ℝ)| * (n : ℝ) ^ (-(11 / 2 : ℝ)) ≤ C * (n : ℝ) ^ (231 / 40 : ℝ) * (n : ℝ) ^ (-(11 / 2 : ℝ)) := by
        gcongr; exact hC n hn
    _ = C * (n : ℝ) ^ (11 / 40 : ℝ) := by
        rw [mul_assoc, ← Real.rpow_add hn0]; norm_num

/-- The key pointwise bound: `|λ(p^{j+a}) λ(p^j)| p^{−j} ≤ C² p^{11a/40} (p^{−9/20})^j`. -/
lemma term_bound {C : ℝ} (hC1 : 1 ≤ C) (hC : ∀ n : ℕ, 1 ≤ n → |lam n| ≤ C * (n : ℝ) ^ (11 / 40 : ℝ))
    {p : ℕ} (hp : p.Prime) (a j : ℕ) :
    |lam (p ^ (j + a)) * lam (p ^ j)| * (p : ℝ) ^ (-(j : ℝ)) ≤
      C ^ 2 * (p : ℝ) ^ ((11 / 40 : ℝ) * a) * ((p : ℝ) ^ (-(9 / 20 : ℝ))) ^ j := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have h1 := hC (p ^ (j + a)) (Nat.one_le_pow _ _ hp.pos)
  have h2 := hC (p ^ j) (Nat.one_le_pow _ _ hp.pos)
  rw [abs_mul]
  have e1 : (((p ^ (j + a) : ℕ) : ℝ)) ^ (11 / 40 : ℝ) = (p : ℝ) ^ ((11 / 40 : ℝ) * (j + a)) := by
    push_cast; rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; push_cast; ring_nf
  have e2 : (((p ^ j : ℕ) : ℝ)) ^ (11 / 40 : ℝ) = (p : ℝ) ^ ((11 / 40 : ℝ) * j) := by
    push_cast; rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; ring_nf
  rw [e1] at h1; rw [e2] at h2
  have e3 : ((p : ℝ) ^ (-(9 / 20 : ℝ))) ^ j = (p : ℝ) ^ (-(9 / 20 : ℝ) * j) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
  rw [e3]
  have hpos : 0 ≤ (p : ℝ) ^ (-(j : ℝ)) := by positivity
  calc |lam (p ^ (j + a))| * |lam (p ^ j)| * (p : ℝ) ^ (-(j : ℝ))
      ≤ (C * (p : ℝ) ^ ((11 / 40 : ℝ) * (j + a))) * (C * (p : ℝ) ^ ((11 / 40 : ℝ) * j)) * (p : ℝ) ^ (-(j : ℝ)) := by
        gcongr
    _ = C ^ 2 * ((p : ℝ) ^ ((11 / 40 : ℝ) * (j + a)) * (p : ℝ) ^ ((11 / 40 : ℝ) * j) * (p : ℝ) ^ (-(j : ℝ))) := by ring
    _ = _ := by
        rw [← Real.rpow_add hp0, ← Real.rpow_add hp0, mul_assoc, ← Real.rpow_add hp0]
        congr 2; ring

lemma ratio_lt {p : ℕ} (hp : p.Prime) : (p : ℝ) ^ (-(9 / 20 : ℝ)) < 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by norm_num)

lemma summable_Np {p : ℕ} (hp : p.Prime) (a : ℕ) :
    Summable fun j : ℕ => lam (p ^ (j + a)) * lam (p ^ j) * (p : ℝ) ^ (-(j : ℝ)) := by
  obtain ⟨C, hC1, hC⟩ := lam_bound
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (by positivity) (ratio_lt hp)).mul_left
      (C ^ 2 * (p : ℝ) ^ ((11 / 40 : ℝ) * a))) (fun j => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ (-(j : ℝ)))]
  exact term_bound hC1 hC hp a j

lemma summable_Np' {p : ℕ} (hp : p.Prime) (a : ℕ) :
    Summable fun j : ℕ => (j : ℝ) * Real.log p * lam (p ^ (j + a)) * lam (p ^ j) * (p : ℝ) ^ (-(j : ℝ)) := by
  obtain ⟨C, hC1, hC⟩ := lam_bound
  have hr := ratio_lt hp
  have hg := summable_pow_mul_geometric_of_norm_lt_one 1
    (show ‖(p : ℝ) ^ (-(9 / 20 : ℝ))‖ < 1 by rw [Real.norm_of_nonneg (by positivity)]; exact hr)
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  refine Summable.of_norm_bounded (hg.mul_left (Real.log p * (C ^ 2 * (p : ℝ) ^ ((11 / 40 : ℝ) * a)))) (fun j => ?_)
  have := term_bound hC1 hC hp a j
  rw [Real.norm_eq_abs]
  have e : |(j : ℝ) * Real.log p * lam (p ^ (j + a)) * lam (p ^ j) * (p : ℝ) ^ (-(j : ℝ))| =
      (j : ℝ) * Real.log p * (|lam (p ^ (j + a)) * lam (p ^ j)| * (p : ℝ) ^ (-(j : ℝ))) := by
    rw [show (j : ℝ) * Real.log p * lam (p ^ (j + a)) * lam (p ^ j) * (p : ℝ) ^ (-(j : ℝ)) =
      ((j : ℝ) * Real.log p) * (lam (p ^ (j + a)) * lam (p ^ j)) * (p : ℝ) ^ (-(j : ℝ)) by ring,
      abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (j : ℝ) * Real.log p),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ (-(j : ℝ)))]
    ring
  rw [e, pow_one]
  have hj : 0 ≤ (j : ℝ) * Real.log p := by positivity
  calc (j : ℝ) * Real.log p * (|lam (p ^ (j + a)) * lam (p ^ j)| * (p : ℝ) ^ (-(j : ℝ)))
      ≤ (j : ℝ) * Real.log p * (C ^ 2 * (p : ℝ) ^ ((11 / 40 : ℝ) * a) * ((p : ℝ) ^ (-(9 / 20 : ℝ))) ^ j) :=
        mul_le_mul_of_nonneg_left this hj
    _ = _ := by ring

lemma summable_Dp {p : ℕ} (hp : p.Prime) :
    Summable fun j : ℕ => lam (p ^ j) ^ 2 * (p : ℝ) ^ (-(j : ℝ)) :=
  (summable_Np hp 0).congr fun j => by rw [Nat.add_zero, sq]

lemma summable_Dp' {p : ℕ} (hp : p.Prime) :
    Summable fun j : ℕ => (j : ℝ) * Real.log p * lam (p ^ j) ^ 2 * (p : ℝ) ^ (-(j : ℝ)) :=
  (summable_Np' hp 0).congr fun j => by rw [Nat.add_zero, sq]; ring

lemma lam_one : lam 1 = 1 := by
  simp [lam, RamanujanTau.SubconvexityCond.lam, RamanujanTau.tau_one]

/-- `D_p ≥ 1`, so `ρ_p = N_p/D_p` is a genuine quotient. -/
theorem one_le_Dp {p : ℕ} (hp : p.Prime) : 1 ≤ Dp p := by
  unfold Dp
  have h := (summable_Dp hp).le_tsum 0 (fun j _ => by positivity)
  simpa [lam_one] using h

end RamanujanTau.HafnerBridge
