import Mathlib

/-!
# A055185: n-th distinct number to appear in A055177; also the n-th to appear in A055194.

Source: https://oeis.org/A055185
Credit: @Solfanbtc

The listed data (5, 1, 2, 3, 4, 6, 8, 10, 9, 11, …) is the list of distinct values, in order of
first appearance, of the cumulative counting sequence (method B) with first term **5**, A055183
(5; 5,1; 5,2,1,1; 5,3,1,3,2,1; …), not of A055177 (first term 3, whose distinct values start
3, 1, 2, 6, 5, …); A055194 (binary matrices) is unrelated. The cross-references in the name are
evidently off; we follow the data. Checked with python3: the first-appearance list of A055183
reproduces the first 54 listed terms.

Construction (A055183, the Mathematica program of A055177 with first term 5): start with `[5]`;
each step appends, for every distinct value `x` already written (in order of first appearance),
the pair `x, c` with `c` the number of occurrences of `x` so far. Each stage is a prefix of the
next.

Conjecture: A055185 is a permutation of the positive integers. A055185 lists each value of
A055183 exactly once (injective by construction), so the conjecture says exactly that every
value of A055183 is positive and every positive integer occurs in A055183. `main` states these
two facts.
-/

namespace OMA.S_oeis_a055185

/-- Distinct elements of a list, in order of first appearance. -/
def firstOcc : List ℕ → List ℕ
  | [] => []
  | x :: l => x :: (firstOcc l).filter (· ≠ x)

/-- One step: append the (value, count) pairs of the distinct values written so far. -/
def step (s : List ℕ) : List ℕ :=
  s ++ (firstOcc s).flatMap (fun x => [x, s.count x])

/-- The terms of A055183 written after `n` steps, starting from `[5]`. -/
def stage (n : ℕ) : List ℕ := step^[n] [5]

/-- A055185 (the first-appearance list of A055183) is a permutation of the positive integers:
its values are positive and every positive integer occurs. -/
theorem main : (∀ n : ℕ, ∀ x ∈ stage n, 0 < x) ∧ (∀ m : ℕ, 0 < m → ∃ n, m ∈ stage n) := by
  sorry

end OMA.S_oeis_a055185
