/-
# Uniform decay for families of `Λ`-series

* `UEnt` — a family of series that is entire with uniform constants; `UDec.conv` — products with a uniformly
  entire family preserve uniform decay.
* `udec_lam` — the family `k ↦ σ_k · Λ_{ℓ(k)}(cb t^{eb} x^d)` decays uniformly when `val σ_k ≥ C(k,2) − C₀`
  and `|ℓ(k)| ≤ |k| + B₀`: with `n = d j` the valuation is `≥ M C(k,2) + N C(j,2) − N(|j| + |ℓ| + 1) − |eb| |j|`.
-/
import RamanujanTau.MTC.LamX

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset

/-- a uniformly entire family. -/
def UEnt (F : ℤ → ℤ → L) : Prop := ∀ A : ℤ, ∃ C : ℤ, ∀ i n, vge (F i n) (A * |n| - C)

lemma UDec.conv {F G : ℤ → ℤ → L} (hF : UEnt F) (hG : UDec G) : UDec (fun i => MTC.conv (F i) (G i)) := by
  intro A
  obtain ⟨C1, h1⟩ := hF (max A 0)
  obtain ⟨C2, h2⟩ := hG (max A 0)
  refine ⟨C1 + C2, fun i n => ?_⟩
  have hFi : Ent (F i) := fun B => by
    obtain ⟨C, hC⟩ := hF B; exact ⟨C, fun k => hC i k⟩
  have hGi : Ent (G i) := hG.ent i
  show vge (MTC.conv (F i) (G i) n) _
  rw [conv_eq hFi hGi]
  refine vge_hs _ fun m => ?_
  refine vge_mono (vge_mul (h1 i m) (h2 i (n - m))) ?_
  have htri : |n| ≤ |m| + |n - m| := by
    have := abs_add_le m (n - m); rwa [add_sub_cancel] at this
  have hA : A * |n| ≤ max A 0 * |n| := mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
  have hB : max A 0 * |n| ≤ max A 0 * (|m| + |n - m|) := mul_le_mul_of_nonneg_left htri (le_max_right _ _)
  nlinarith [le_max_right A 0]

lemma vge_lam0S {N : ℕ} (hN : 1 ≤ N) (p : ℤ) : vge (lam0S hN p) (N * c2 (p + 1) - N * |p|) := by
  refine vge_mono (vge_Θlo hN p) ?_
  have e1 := c2_succ p
  have hN' : (0 : ℤ) ≤ N := by positivity
  have hp : p ≤ |p| := le_abs_self p
  have h1 : (0 : ℤ) ≤ N * |p| := mul_nonneg hN' (abs_nonneg p)
  have h2 : (0 : ℤ) ≤ N * (|p| - p) := mul_nonneg hN' (by linarith)
  rcases min_cases (c2 p) (c2 (p + 1)) with ⟨hm, _⟩ | ⟨hm, _⟩ <;> rw [hm] <;> nlinarith

lemma c2_add (a b : ℤ) : c2 (a + b) = c2 a + c2 b + a * b := by
  have e1 := two_c2 (a + b); have e2 := two_c2 a; have e3 := two_c2 b
  exact mul_left_cancel₀ two_ne_zero (by linear_combination e1 - e2 - e3)

/-- **uniform decay of the `Λ`-family**. -/
theorem udec_lam {N : ℕ} (hN : 1 ≤ N) {d : ℤ} (hd : d ≠ 0) (eb : ℤ → ℤ) (Eb : ℤ) (hEb : ∀ k, |eb k| ≤ Eb)
    (cb : ℂ) (ℓ : ℤ → ℤ) (B0 : ℤ)
    (hℓ : ∀ k, |ℓ k| ≤ |k| + B0) (σ : ℤ → L) {M : ℤ} (hM : 1 ≤ M) (C0 : ℤ)
    (hσ : ∀ k, vge (σ k) (M * c2 k - C0)) :
    UDec (fun k n => σ k * lamX hN (ℓ k) d (eb k) cb n) := by
  intro A
  have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
  obtain ⟨Ck, hCk⟩ := quad_dom hM (N + 1)
  obtain ⟨Cj, hCj⟩ := quad_dom hN' (|A| * |d| + N + Eb)
  refine ⟨Ck + Cj + N * B0 + N + C0, fun k n => ?_⟩
  unfold lamX
  simp only [shiftS, subst]
  split_ifs with hdv
  · obtain ⟨m, hm⟩ := hdv
    have hj : d ∣ n := ⟨m - (ℓ k - 1), by linear_combination hm⟩
    obtain ⟨j, rfl⟩ := hj
    have hmj : m = j + ℓ k - 1 := by
      have : d * m = d * (j + ℓ k - 1) := by linear_combination -hm
      exact mul_left_cancel₀ hd this
    rw [hm, Int.mul_ediv_cancel_left _ hd, hmj]
    refine vge_mono (vge_mul (hσ k) (vge_mul (vge_single _ _) (vge_mul (vge_lam0S hN _) (vge_single _ _)))) ?_
    have e1 := c2_add j (ℓ k)
    have hjl : |j + ℓ k - 1| ≤ |j| + |ℓ k| + 1 := by
      have := le_abs_self j; have := neg_abs_le j; have := le_abs_self (ℓ k); have := neg_abs_le (ℓ k)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hA : A * |d * j| ≤ |A| * |d| * |j| := by
      rw [abs_mul, ← mul_assoc]; exact (le_abs_self _).trans (by rw [abs_mul, abs_mul, abs_abs, abs_abs])
    have hebj : -(Eb * |j|) ≤ eb k * j := by
      have h1 : -(|eb k| * |j|) ≤ eb k * j := by rw [← abs_mul]; exact neg_abs_le _
      have h2 : |eb k| * |j| ≤ Eb * |j| := mul_le_mul_of_nonneg_right (hEb k) (abs_nonneg j)
      linarith
    have h1 := hCk k; have h2 := hCj j; have h3 := hℓ k
    have hNl : (N : ℤ) * |ℓ k| ≤ N * (|k| + B0) := mul_le_mul_of_nonneg_left h3 (by positivity)
    have hNjl : (N : ℤ) * |j + ℓ k - 1| ≤ N * (|j| + |ℓ k| + 1) := mul_le_mul_of_nonneg_left hjl (by positivity)
    rw [show j + ℓ k - 1 + 1 = j + ℓ k by ring, e1]
    nlinarith [abs_nonneg j, abs_nonneg k, abs_nonneg A, abs_nonneg d]
  · simp only [mul_zero]
    exact vge_zero _

/-- a family taking values among finitely many entire series is uniformly entire. -/
lemma uent_of_fin (H : ℤ → ℤ → L) (f : ℤ → ℤ) (S : Finset ℤ) (hf : ∀ k, f k ∈ S) (hH : ∀ s ∈ S, Ent (H s)) :
    UEnt (fun k => H (f k)) := by
  classical
  intro A
  have h : ∀ s ∈ S, ∃ C : ℤ, ∀ n, vge (H s n) (A * |n| - C) := fun s hs => hH s hs A
  choose! C hC using h
  refine ⟨∑ s ∈ S, |C s|, fun k n => vge_mono (hC (f k) (hf k) n) ?_⟩
  have := Finset.single_le_sum (f := fun s => |C s|) (fun _ _ => abs_nonneg _) (hf k)
  have := le_abs_self (C (f k))
  simp only at *
  linarith

end MTC
