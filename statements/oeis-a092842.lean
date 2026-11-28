import Mathlib

/-!
# A092842: the solution x of A073666(x) = n.

Source: https://oeis.org/A092842
Credit: @Solfanbtc

A073666 is the greedy sequence `b(1) = 1`, and `b(k)` is the smallest positive integer not
used earlier such that `b(k-1) * b(k) + 1` is prime (as in the entry's Mathematica and PARI
programs; such an integer exists by Dirichlet's theorem, so the infimum below is the
genuine minimum). `L k` is the list `[b(1), …, b(k)]`. The terms of A073666 are distinct, and
A092842(n) is the unique `x` with `b(x) = n`.

Conjecture (entry): this sequence is infinite, i.e. it is defined for every `n`. That is,
every positive integer `n` occurs in A073666 (which is then a genuine rearrangement of the
natural numbers, as its name says). Checked with python3: the greedy rule reproduces the
listed terms of A073666 and of A092842, and every `n ≤ 10000` occurs among the first 30000
terms of A073666.
-/

namespace OMA.S_oeis_a092842

/-- `L k = [b(1), …, b(k)]` for A073666 (`L 0 = []`). -/
noncomputable def L : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | k + 2 =>
    let l := L (k + 1)
    l ++ [sInf {m : ℕ | 1 ≤ m ∧ m ∉ l ∧ (l.getLastD 1 * m + 1).Prime}]

/-- The conjecture: every positive integer occurs in A073666. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, n ∈ L k := by
  sorry

end OMA.S_oeis_a092842
