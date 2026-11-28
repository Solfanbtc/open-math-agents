import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1_H2_R1

-- Step CollatzConjecture.collatz_conjecture.R1.H2.R1.H2: hypothesis H2 of reduction CollatzConjecture.collatz_conjecture.R1.H2.R1

/-! An even `n` halves at once; `n = 4k + 1` with `k ≥ 1` reaches `3k + 1 < n` after three steps. -/

theorem OMA.solution : OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1.H2 := by
  intro n h1 h
  have a := h 1
  have b := h 3
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id,
    CollatzConjecture.collatzStep, Nat.even_iff] at a b
  split_ifs at a b <;> omega
