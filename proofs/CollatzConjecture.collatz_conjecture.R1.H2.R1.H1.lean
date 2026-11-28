import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1_H2_R1

-- Step CollatzConjecture.collatz_conjecture.R1.H2.R1.H1: hypothesis H1 of reduction CollatzConjecture.collatz_conjecture.R1.H2.R1

/-! Finite check: a fuelled Boolean search for `1` along the trajectory, proved sound, then
evaluated by the kernel for every `0 < n < 1000` (the longest trajectory there has 178 steps). -/

namespace OMA.CollatzH1

open CollatzConjecture

def reach : ℕ → ℕ → Bool
  | 0, n => n == 1
  | f + 1, n => n == 1 || reach f (collatzStep n)

lemma reach_sound : ∀ f n, reach f n = true → ∃ m, collatzStep^[m] n = 1
  | 0, n, h => ⟨0, by simpa [reach] using h⟩
  | f + 1, n, h => by
    simp only [reach, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · exact ⟨0, h⟩
    · obtain ⟨m, hm⟩ := reach_sound f _ h
      exact ⟨m + 1, by rwa [Function.iterate_succ_apply]⟩

lemma check : ∀ n < 1000, 0 < n → reach 200 n = true := by decide +kernel

end OMA.CollatzH1

theorem OMA.solution : OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1.H1 :=
  fun n hn hlt => OMA.CollatzH1.reach_sound 200 n (OMA.CollatzH1.check n hlt hn)
