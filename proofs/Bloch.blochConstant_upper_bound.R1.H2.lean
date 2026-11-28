import OMAReductions.R_Bloch_blochConstant_upper_bound_R1

-- Step Bloch.blochConstant_upper_bound.R1.H2: hypothesis H2 of reduction Bloch.blochConstant_upper_bound.R1
-- Credit: @Solfanbtc

/-! The lattice points are `c - (3 c / 2) s + i (c √3 / 2) t` with `s = m + n` and `t = m - n`,
two integers of the same parity. Write `x = c - (3 c / 2) P + i (c √3 / 2) Q`, round `P` and `Q`
down and take the better of two opposite corners of the rhombus of admissible `(s, t)` around
`(P, Q)`: the coordinate errors `a, b` then satisfy `9 a ^ 2 + 3 b ^ 2 ≤ 4`, so the distance
`(c / 2) √(9 a ^ 2 + 3 b ^ 2)` is at most `c < r`. -/

namespace OMA.BlochH2

/-- The rhombus estimate: on the triangle `a, b ≥ 0`, `b ≤ 1`, `3 a + b ≤ 2`. -/
lemma key {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hb1 : b ≤ 1) (h : 3 * a + b ≤ 2) :
    9 * a ^ 2 + 3 * b ^ 2 ≤ 4 := by
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 - b - 3 * a)
    (by linarith : (0 : ℝ) ≤ 2 - b + 3 * a), mul_nonneg hb (by linarith : (0 : ℝ) ≤ 1 - b)]

/-- Every point `(P, Q)` is close to some `(m + n, m - n)`. -/
lemma exists_mn (P Q : ℝ) :
    ∃ m n : ℤ, 9 * (P - ((m : ℝ) + n)) ^ 2 + 3 * (Q - ((m : ℝ) - n)) ^ 2 ≤ 4 := by
  have hP0 : ((⌊P⌋ : ℤ) : ℝ) ≤ P := Int.floor_le P
  have hP1 : P < ((⌊P⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one P
  have hQ0 : ((⌊Q⌋ : ℤ) : ℝ) ≤ Q := Int.floor_le Q
  have hQ1 : Q < ((⌊Q⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one Q
  rcases Int.even_or_odd (⌊P⌋ - ⌊Q⌋) with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hk' : ((⌊P⌋ : ℤ) : ℝ) = (⌊Q⌋ : ℝ) + k + k := by
      have : ⌊P⌋ = ⌊Q⌋ + k + k := by omega
      exact_mod_cast this
    by_cases h : 3 * (P - ⌊P⌋) + (Q - ⌊Q⌋) ≤ 2
    · refine ⟨⌊Q⌋ + k, k, ?_⟩
      have e1 : P - (((⌊Q⌋ + k : ℤ) : ℝ) + k) = P - ⌊P⌋ := by push_cast; linarith
      have e2 : Q - (((⌊Q⌋ + k : ℤ) : ℝ) - k) = Q - ⌊Q⌋ := by push_cast; ring
      rw [e1, e2]
      exact key (by linarith) (by linarith) (by linarith) h
    · refine ⟨⌊Q⌋ + k + 1, k, ?_⟩
      have e1 : P - (((⌊Q⌋ + k + 1 : ℤ) : ℝ) + k) = -(1 - (P - ⌊P⌋)) := by push_cast; linarith
      have e2 : Q - (((⌊Q⌋ + k + 1 : ℤ) : ℝ) - k) = -(1 - (Q - ⌊Q⌋)) := by push_cast; ring
      rw [e1, e2, neg_sq, neg_sq]
      exact key (by linarith) (by linarith) (by linarith) (by linarith)
  · have hk' : ((⌊P⌋ : ℤ) : ℝ) = (⌊Q⌋ : ℝ) + 2 * k + 1 := by
      have : ⌊P⌋ = ⌊Q⌋ + 2 * k + 1 := by omega
      exact_mod_cast this
    by_cases h : 3 * (1 - (P - ⌊P⌋)) + (Q - ⌊Q⌋) ≤ 2
    · refine ⟨⌊Q⌋ + k + 1, k + 1, ?_⟩
      have e1 : P - (((⌊Q⌋ + k + 1 : ℤ) : ℝ) + ((k + 1 : ℤ) : ℝ)) = -(1 - (P - ⌊P⌋)) := by
        push_cast; linarith
      have e2 : Q - (((⌊Q⌋ + k + 1 : ℤ) : ℝ) - ((k + 1 : ℤ) : ℝ)) = Q - ⌊Q⌋ := by push_cast; ring
      rw [e1, e2, neg_sq]
      exact key (by linarith) (by linarith) (by linarith) h
    · refine ⟨⌊Q⌋ + 1 + k, k, ?_⟩
      have e1 : P - (((⌊Q⌋ + 1 + k : ℤ) : ℝ) + k) = P - ⌊P⌋ := by push_cast; linarith
      have e2 : Q - (((⌊Q⌋ + 1 + k : ℤ) : ℝ) - k) = -(1 - (Q - ⌊Q⌋)) := by push_cast; ring
      rw [e1, e2, neg_sq]
      exact key (by linarith) (by linarith) (by linarith) (by linarith)

end OMA.BlochH2

open OMA.BlochH2 in
theorem OMA.solution : OMA.R_Bloch_blochConstant_upper_bound_R1.H2 := by
  intro c hc x r hcr
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  obtain ⟨m, n, hmn⟩ := exists_mn (2 * (c - x.re) / (3 * c)) (2 * x.im / (c * Real.sqrt 3))
  refine ⟨_, ⟨m, n, rfl⟩, ?_⟩
  rw [Metric.mem_ball, Complex.dist_eq]
  set z := ((c : ℝ) : ℂ) * (1 + (m : ℂ) * ((⟨-1 / 2, Real.sqrt 3 / 2⟩ : ℂ) - 1) +
    (n : ℂ) * ((⟨-1 / 2, Real.sqrt 3 / 2⟩ : ℂ) ^ 2 - 1)) - x with hz
  have hre : z.re = 3 * c / 2 * (2 * (c - x.re) / (3 * c) - ((m : ℝ) + n)) := by
    rw [hz]
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.one_re,
      Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im,
      sq, Complex.sub_im, Complex.add_im]
    field_simp
    linear_combination (-(c * n)) * hs
  have him : z.im = c * Real.sqrt 3 / 2 * (((m : ℝ) - n) - 2 * x.im / (c * Real.sqrt 3)) := by
    rw [hz]
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.one_re,
      Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im,
      sq, Complex.sub_im, Complex.add_im]
    field_simp
    ring
  have hsq : ‖z‖ ^ 2 ≤ c ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    set a := 2 * (c - x.re) / (3 * c) - ((m : ℝ) + n)
    set b := 2 * x.im / (c * Real.sqrt 3) - ((m : ℝ) - n)
    have hb : ((m : ℝ) - n) - 2 * x.im / (c * Real.sqrt 3) = -b := by ring
    rw [hb]
    have h3 : 3 * c / 2 * a * (3 * c / 2 * a) + c * Real.sqrt 3 / 2 * -b * (c * Real.sqrt 3 / 2 * -b)
        = c ^ 2 / 4 * (9 * a ^ 2 + 3 * b ^ 2) := by
      linear_combination (c ^ 2 * b ^ 2 / 4) * hs
    rw [h3]
    nlinarith [sq_nonneg c]
  by_contra hcon
  have hrz : r ≤ ‖z‖ := not_lt.mp hcon
  nlinarith [norm_nonneg z]
