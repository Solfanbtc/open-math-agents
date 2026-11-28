import OMAReductions.R_LittlewoodConjecture_littlewood_conjecture_R1

-- Step LittlewoodConjecture.littlewood_conjecture.R1.H1: hypothesis H1 of reduction LittlewoodConjecture.littlewood_conjecture.R1
-- Credit: @Solfanbtc

/-! For a rational `α = q`, the term vanishes at every multiple `n` of the denominator of `q`
(`n α` is then an integer), and all terms are nonnegative: so the sequence is bounded below by
`0` and frequently equal to `0`, and its `liminf` is `0`. -/

open Filter

theorem OMA.solution : OMA.R_LittlewoodConjecture_littlewood_conjecture_R1.H1 := by
  intro α β ⟨q, hq⟩
  have hd0 : ∀ m : ℤ, distToNearestInt (m : ℝ) = 0 := fun m => by simp [distToNearestInt]
  have hnonneg : ∀ n : ℕ,
      0 ≤ (n : ℝ) * distToNearestInt (n * α) * distToNearestInt (n * β) := fun n =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (distToNearestInt_nonneg _))
      (distToNearestInt_nonneg _)
  have hzero : ∀ k : ℕ, ((k * q.den : ℕ) : ℝ) * distToNearestInt ((k * q.den : ℕ) * α) *
      distToNearestInt ((k * q.den : ℕ) * β) = 0 := by
    intro k
    have hint : ((k * q.den : ℕ) : ℝ) * α = ((k * q.num : ℤ) : ℝ) := by
      have hden : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
      rw [hq, Rat.cast_def]
      push_cast
      field_simp
    rw [hint, hd0, mul_zero, zero_mul]
  have hfreq : ∃ᶠ n : ℕ in atTop,
      (n : ℝ) * distToNearestInt (n * α) * distToNearestInt (n * β) = 0 := by
    rw [frequently_atTop]
    intro a
    refine ⟨a * q.den, ?_, hzero a⟩
    have := q.den_pos
    nlinarith
  apply le_antisymm
  · exact liminf_le_of_frequently_le (hfreq.mono fun n h => h.le)
      (isBoundedUnder_of ⟨0, hnonneg⟩)
  · refine le_liminf_of_le ⟨0, fun a ha => ?_⟩ (Eventually.of_forall hnonneg)
    rw [eventually_map] at ha
    obtain ⟨n, h1, h2⟩ := (ha.and_frequently hfreq).exists
    linarith
