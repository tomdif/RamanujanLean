/-- `S47a`: `B = (2 0; 0 1)`, shifts `i (1, 0)`, `i ∈ {0, 1}`. -/
def B47a : ECS where
  b11 := 2
  b12 := 0
  b21 := 0
  b22 := 1
  r1 := 1
  r2 := 0
  I := {0, 1}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 0 * n - 0) % 2 + 0), by simp only [mem_insert, mem_singleton]; omega,
    ((1 * (m - 1 * ((1 * m + 0 * n - 0) % 2 + 0)) - 0 * (n - 0 * ((1 * m + 0 * n - 0) % 2 + 0))) / 2), ((2 * (n - 0 * ((1 * m + 0 * n - 0) % 2 + 0)) - 0 * (m - 1 * ((1 * m + 0 * n - 0) % 2 + 0))) / 2), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem S47a : QS (qmono 4 1 12 0 0 0 0) = QS (qmono 16 2 12 0 0 0 0) + mono 4 1 * QS (qmono 16 2 12 16 2 0 0) := by
  have h := QS_sub 4 1 12 0 0 0 0 B47a (fun i hi => by
    simp only [B47a, mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl <;> exact qmono_summ _ _ _ _ _ _ _ (by norm_num [sA, B47a])
      (by norm_num [sA, sB, sC, B47a]))
  simp only [B47a] at h
  rw [sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, sA, sB, sC, sd, se] at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `S47b`: `B = (1 1; -1 1)`, shifts `i (1, 0)`, `i ∈ {0, 1}`. -/
def B47b : ECS where
  b11 := 1
  b12 := 1
  b21 := (-1)
  b22 := 1
  r1 := 1
  r2 := 0
  I := {0, 1}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 1 * n - 0) % 2 + 0), by simp only [mem_insert, mem_singleton]; omega,
    ((1 * (m - 1 * ((1 * m + 1 * n - 0) % 2 + 0)) - 1 * (n - 0 * ((1 * m + 1 * n - 0) % 2 + 0))) / 2), ((1 * (n - 0 * ((1 * m + 1 * n - 0) % 2 + 0)) - (-1) * (m - 1 * ((1 * m + 1 * n - 0) % 2 + 0))) / 2), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem S47b : QS (qmono 6 1 8 0 0 0 0) = QS (qmono 12 (-2) 16 0 0 0 0) + mono 6 1 * QS (qmono 12 (-2) 16 10 14 0 0) := by
  have h := QS_sub 6 1 8 0 0 0 0 B47b (fun i hi => by
    simp only [B47b, mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl <;> exact qmono_summ _ _ _ _ _ _ _ (by norm_num [sA, B47b])
      (by norm_num [sA, sB, sC, B47b]))
  simp only [B47b] at h
  rw [sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, sA, sB, sC, sd, se] at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `S47c`: `B = (2 0; 0 1)`, shifts `i (1, 0)`, `i ∈ {0, 1}`. -/
def B47c : ECS where
  b11 := 2
  b12 := 0
  b21 := 0
  b22 := 1
  r1 := 1
  r2 := 0
  I := {0, 1}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 0 * n - 0) % 2 + 0), by simp only [mem_insert, mem_singleton]; omega,
    ((1 * (m - 1 * ((1 * m + 0 * n - 0) % 2 + 0)) - 0 * (n - 0 * ((1 * m + 0 * n - 0) % 2 + 0))) / 2), ((2 * (n - 0 * ((1 * m + 0 * n - 0) % 2 + 0)) - 0 * (m - 1 * ((1 * m + 0 * n - 0) % 2 + 0))) / 2), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem S47c : QS (qmono 3 1 16 1 16 1 0) = QS (qmono 12 2 16 2 16 0 0) - mono 4 1 * QS (qmono 12 2 16 14 18 0 0) := by
  have h := QS_sub 3 1 16 1 16 1 0 B47c (fun i hi => by
    simp only [B47c, mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl <;> exact qmono_summ _ _ _ _ _ _ _ (by norm_num [sA, B47c])
      (by norm_num [sA, sB, sC, B47c]))
  simp only [B47c] at h
  rw [sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, sA, sB, sC, sd, se] at h
  simp only [qmono_par 12 2 16 2 16 2 0 0 0 (by decide) (by decide), qmono_par 12 2 16 14 18 2 0 0 0 (by decide) (by decide)] at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `S47r`: `B = (0 1; -1 0)`, shifts `i (0, 0)`, `i ∈ {0}`. -/
def B47r : ECS where
  b11 := 0
  b12 := 1
  b21 := (-1)
  b22 := 0
  r1 := 0
  r2 := 0
  I := {0}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 0 * n - 0) % 1 + 0), by simp only [mem_insert, mem_singleton]; omega,
    ((0 * (m - 0 * ((0 * m + 0 * n - 0) % 1 + 0)) - 1 * (n - 0 * ((0 * m + 0 * n - 0) % 1 + 0))) / 1), ((0 * (n - 0 * ((0 * m + 0 * n - 0) % 1 + 0)) - (-1) * (m - 0 * ((0 * m + 0 * n - 0) % 1 + 0))) / 1), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem S47r : QS (qmono 16 2 12 0 0 0 0) = QS (qmono 12 (-2) 16 0 0 0 0) := by
  have h := QS_sub 16 2 12 0 0 0 0 B47r (fun i hi => by
    simp only [B47r, mem_insert, mem_singleton] at hi
    rcases hi with rfl <;> exact qmono_summ _ _ _ _ _ _ _ (by norm_num [sA, B47r])
      (by norm_num [sA, sB, sC, B47r]))
  simp only [B47r] at h
  rw [sum_singleton] at h
  norm_num [qf0, sA, sB, sC, sd, se] at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `S47s`: `B = (0 1; 1 0)`, shifts `i (0, 0)`, `i ∈ {0}`. -/
def B47s : ECS where
  b11 := 0
  b12 := 1
  b21 := 1
  b22 := 0
  r1 := 0
  r2 := 0
  I := {0}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 0 * n - 0) % 1 + 0), by simp only [mem_insert, mem_singleton]; omega,
    ((0 * (m - 0 * ((0 * m + 0 * n - 0) % 1 + 0)) - 1 * (n - 0 * ((0 * m + 0 * n - 0) % 1 + 0))) / (-1)), ((0 * (n - 0 * ((0 * m + 0 * n - 0) % 1 + 0)) - 1 * (m - 0 * ((0 * m + 0 * n - 0) % 1 + 0))) / (-1)), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem S47s : QS (qmono 16 2 12 16 2 0 0) = QS (qmono 12 2 16 2 16 0 0) := by
  have h := QS_sub 16 2 12 16 2 0 0 B47s (fun i hi => by
    simp only [B47s, mem_insert, mem_singleton] at hi
    rcases hi with rfl <;> exact qmono_summ _ _ _ _ _ _ _ (by norm_num [sA, B47s])
      (by norm_num [sA, sB, sC, B47s]))
  simp only [B47s] at h
  rw [sum_singleton] at h
  norm_num [qf0, sA, sB, sC, sd, se] at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `S47t`: `B = (-1 0; 0 1)`, shifts `i (-1, 0)`, `i ∈ {1}`. -/
def B47t : ECS where
  b11 := (-1)
  b12 := 0
  b21 := 0
  b22 := 1
  r1 := (-1)
  r2 := 0
  I := {1}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 0 * n - 1) % 1 + 1), by simp only [mem_insert, mem_singleton]; omega,
    ((1 * (m - (-1) * ((0 * m + 0 * n - 1) % 1 + 1)) - 0 * (n - 0 * ((0 * m + 0 * n - 1) % 1 + 1))) / (-1)), (((-1) * (n - 0 * ((0 * m + 0 * n - 1) % 1 + 1)) - 0 * (m - (-1) * ((0 * m + 0 * n - 1) % 1 + 1))) / (-1)), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem S47t : QS (qmono 12 (-2) 16 10 14 0 0) = mono 2 1 * QS (qmono 12 2 16 14 18 0 0) := by
  have h := QS_sub 12 (-2) 16 10 14 0 0 B47t (fun i hi => by
    simp only [B47t, mem_insert, mem_singleton] at hi
    rcases hi with rfl <;> exact qmono_summ _ _ _ _ _ _ _ (by norm_num [sA, B47t])
      (by norm_num [sA, sB, sC, B47t]))
  simp only [B47t] at h
  rw [sum_singleton] at h
  norm_num [qf0, sA, sB, sC, sd, se] at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `LA47`: `B = (1 -1; 0 4)`, shifts `i (0, 1)`, `i ∈ {(-4), (-3), (-2), (-1)}`. -/
def BA47 : ECS where
  b11 := 1
  b12 := (-1)
  b21 := 0
  b22 := 4
  r1 := 0
  r2 := 1
  I := {(-4), (-3), (-2), (-1)}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 1 * n - (-4)) % 4 + (-4)), by simp only [mem_insert, mem_singleton]; omega,
    ((4 * (m - 0 * ((0 * m + 1 * n - (-4)) % 4 + (-4))) - (-1) * (n - 1 * ((0 * m + 1 * n - (-4)) % 4 + (-4)))) / 4), ((1 * (n - 1 * ((0 * m + 1 * n - (-4)) % 4 + (-4))) - 0 * (m - 0 * ((0 * m + 1 * n - (-4)) % 4 + (-4)))) / 4), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem LA47 : QS (qmono 4 1 12 0 0 0 0) = (θ hm8 4 (-1) * θ hm376 188 (-1)) + 2 * (mono 12 1 * (θ hm8 2 (-1) * θ hm376 94 (-1))) + (mono 48 1 * (θ hm8 0 (-1) * θ hm376 0 (-1))) := by
  have h := (QS_orth 4 1 12 0 0 0 0 BA47 hm8 hm376 (by norm_num [BA47])
    (by norm_num [BA47]) (by norm_num [BA47])).2
  simp only [BA47] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfrm hm376 94 (-1) (-94) 1 (e := (-94)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm8 2 (-1) (-2) 1 (e := (-2)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm376 188 (-1) (by norm_num : (-1 : ℂ) ≠ 0) (-188) 1 (e := (-188)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm8 4 (-1) (by norm_num : (-1 : ℂ) ≠ 0) (-4) 1 (e := (-4)) (by norm_num) (by norm_num [c2]) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `LB47`: `B = (1 -1; 0 6)`, shifts `i (0, 1)`, `i ∈ {(-6), (-5), (-4), (-3), (-2), (-1)}`. -/
def BB47 : ECS where
  b11 := 1
  b12 := (-1)
  b21 := 0
  b22 := 6
  r1 := 0
  r2 := 1
  I := {(-6), (-5), (-4), (-3), (-2), (-1)}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 1 * n - (-6)) % 6 + (-6)), by simp only [mem_insert, mem_singleton]; omega,
    ((6 * (m - 0 * ((0 * m + 1 * n - (-6)) % 6 + (-6))) - (-1) * (n - 1 * ((0 * m + 1 * n - (-6)) % 6 + (-6)))) / 6), ((1 * (n - 1 * ((0 * m + 1 * n - (-6)) % 6 + (-6))) - 0 * (m - 0 * ((0 * m + 1 * n - (-6)) % 6 + (-6)))) / 6), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem LB47 : QS (qmono 6 1 8 0 0 0 0) = (θ hm12 6 (-1) * θ hm564 282 (-1)) + 2 * (mono 8 1 * (θ hm12 4 (-1) * θ hm564 188 (-1))) + 2 * (mono 32 1 * (θ hm12 2 (-1) * θ hm564 94 (-1))) + (mono 72 1 * (θ hm12 0 (-1) * θ hm564 0 (-1))) := by
  have h := (QS_orth 6 1 8 0 0 0 0 BB47 hm12 hm564 (by norm_num [BB47])
    (by norm_num [BB47]) (by norm_num [BB47])).2
  simp only [BB47] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfrm hm12 2 (-1) (-2) 1 (e := (-2)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm12 4 (-1) (-4) 1 (e := (-4)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm564 188 (-1) (-188) 1 (e := (-188)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm564 94 (-1) (-94) 1 (e := (-94)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm12 6 (-1) (by norm_num : (-1 : ℂ) ≠ 0) (-6) 1 (e := (-6)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm564 282 (-1) (by norm_num : (-1 : ℂ) ≠ 0) (-282) 1 (e := (-282)) (by norm_num) (by norm_num [c2]) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `LC47`: `B = (1 -1; 0 3)`, shifts `i (0, 1)`, `i ∈ {(-3), (-2), (-1)}`. -/
def BC47 : ECS where
  b11 := 1
  b12 := (-1)
  b21 := 0
  b22 := 3
  r1 := 0
  r2 := 1
  I := {(-3), (-2), (-1)}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 1 * n - (-3)) % 3 + (-3)), by simp only [mem_insert, mem_singleton]; omega,
    ((3 * (m - 0 * ((0 * m + 1 * n - (-3)) % 3 + (-3))) - (-1) * (n - 1 * ((0 * m + 1 * n - (-3)) % 3 + (-3)))) / 3), ((1 * (n - 1 * ((0 * m + 1 * n - (-3)) % 3 + (-3))) - 0 * (m - 0 * ((0 * m + 1 * n - (-3)) % 3 + (-3)))) / 3), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem LC47 : QS (qmono 3 1 16 1 16 1 0) = 2 * (θ hm6 2 1 * θ hm282 94 1) := by
  have h := (QS_orth 3 1 16 1 16 1 0 BC47 hm6 hm282 (by norm_num [BC47])
    (by norm_num [BC47]) (by norm_num [BC47])).2
  simp only [BC47] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfr1 hm282 94 (-1) (-94) (-1) (e := (-94)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm6 2 (-1) (-2) (-1) (e := (-2)) (by norm_num) (by norm_num [c2]) (by norm_num), θz' hm282 0 (e := 0) (by norm_num), θz' hm6 0 (e := 0) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h
