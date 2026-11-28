import OMAReductions.R_JugglerConjecture_juggler_conjecture_R1

-- Step JugglerConjecture.juggler_conjecture.R1.H1: hypothesis H1 of reduction JugglerConjecture.juggler_conjecture.R1
-- Credit: @Solfanbtc

/-! Finite check. The juggler step is rewritten with integer square roots
(`⌊n ^ (1/2)⌋ = Nat.sqrt n` and `⌊n ^ (3/2)⌋ = Nat.sqrt (n ^ 3)`), then a fuelled Boolean search
for `1` along the trajectory, proved sound, is evaluated by the kernel for every `0 < n ≤ 1000`
(the longest trajectory there has 73 steps, from `n = 193`). -/

namespace OMA.JugglerH1

/-- The juggler step with integer square roots. -/
def jstep (n : ℕ) : ℕ := if n % 2 = 0 then Nat.sqrt n else Nat.sqrt (n ^ 3)

lemma jugglerStep_eq (n : ℕ) : JugglerConjecture.jugglerStep n = jstep n := by
  unfold JugglerConjecture.jugglerStep jstep
  by_cases h : Even n
  · rw [if_pos h, if_pos (Nat.even_iff.mp h), ← Real.sqrt_eq_rpow,
      Real.nat_floor_real_sqrt_eq_nat_sqrt]
  · have h' : ¬ n % 2 = 0 := fun h2 => h (Nat.even_iff.mpr h2)
    have e : (n : ℝ) ^ (3 / 2 : ℝ) = Real.sqrt ((n ^ 3 : ℕ) : ℝ) := by
      rw [Real.sqrt_eq_rpow, Nat.cast_pow, ← Real.rpow_natCast,
        ← Real.rpow_mul (Nat.cast_nonneg n)]
      norm_num
    rw [if_neg h, if_neg h', e, Real.nat_floor_real_sqrt_eq_nat_sqrt]

def reach : ℕ → ℕ → Bool
  | 0, n => n == 1
  | f + 1, n => n == 1 || reach f (jstep n)

lemma reach_sound : ∀ f n, reach f n = true → ∃ m, JugglerConjecture.jugglerStep^[m] n = 1
  | 0, n, h => ⟨0, by simpa [reach] using h⟩
  | f + 1, n, h => by
    simp only [reach, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · exact ⟨0, h⟩
    · obtain ⟨m, hm⟩ := reach_sound f _ h
      exact ⟨m + 1, by rw [Function.iterate_succ_apply, jugglerStep_eq]; exact hm⟩

lemma check : ∀ n ≤ 1000, 0 < n → reach 80 n = true := by decide +kernel

end OMA.JugglerH1

theorem OMA.solution : OMA.R_JugglerConjecture_juggler_conjecture_R1.H1 :=
  fun n hn hle => OMA.JugglerH1.reach_sound 80 n (OMA.JugglerH1.check n hle hn)
