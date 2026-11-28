import Mathlib

/-!
# A083518: Beginning with 3, a(i) a(j) + 2 is prime for all i ≠ j

Source: https://oeis.org/A083518
Credit: @Solfanbtc

The greedy sequence: `a(1) = 3`, and each next term is the smallest number greater than the previous
term such that `a(i) · a(n) + 2` is prime for every earlier term `a(i)`:
`3, 5, 7, 27, 45, 495, 3615, 16695, 533445, 832305, …` (a greedy search with this rule reproduces the
first 10 data terms). Below `terms k = [a(1), …, a(k+1)]` as long as the sequence continues.

Conjecture (OEIS comment): the sequence is finite, i.e. the greedy construction stops: for some
`k`, no number larger than the last term of `terms k` forms a prime `x m + 2` with every term `x`.
-/

namespace OMA.S_oeis_a083518

/-- `m` can follow the terms `l`: it exceeds the last term and `x m + 2` is prime for all `x ∈ l`. -/
def Admissible (l : List ℕ) (m : ℕ) : Prop := l.getLastD 0 < m ∧ ∀ x ∈ l, (x * m + 2).Prime

/-- The greedy next term. -/
noncomputable def next (l : List ℕ) : ℕ := sInf {m : ℕ | Admissible l m}

/-- `terms k = [a(1), …, a(k+1)]`. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => [3]
  | k + 1 => terms k ++ [next (terms k)]

/-- The sequence is finite: at some stage no admissible next term exists. -/
theorem main : ∃ k : ℕ, ¬ ∃ m : ℕ, Admissible (terms k) m := by
  sorry

end OMA.S_oeis_a083518
