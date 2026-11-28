import Mathlib

/-!
# A011848: a(n) = floor(binomial(n, 2)/2).

Source: https://oeis.org/A011848
Credit: @Solfanbtc

Conjecture (Peter Kagey, Nov 18 2016), as printed in the entry: "For n = 2, a(n) is the
greatest k such that A123663(k) < A000217(n - 2)."

The printed "n = 2" is read as "n >= 2" (a lost inequality sign): for the single value
`n = 2` the claim says nothing about the sequence, and `A000217(0) = 0`, so no `k ≥ 1`
(A123663 has offset 1 and nonnegative terms) satisfies `A123663(k) < 0`; the greatest such
`k` does not exist there while `a(2) = 0`. The minimal fix is to state the conjecture for
`n ≥ 3`, where it was checked in Python for `3 ≤ n < 400`.

Definitions:
* `a n = ⌊binomial(n,2) / 2⌋` (A011848, offset 0).
* `sharedEdges k = 2k - ⌈2 √k⌉` for `k ≥ 1`: A123663, the number of shared edges in a spiral
  of `k` unit squares, by the formula of J. F. Fleron in that entry (from Harary and Harborth).
* `tri m = m (m + 1) / 2` (A000217).
-/

namespace OMA.S_oeis_a011848

/-- A011848: `⌊binomial(n, 2) / 2⌋`. -/
def a (n : ℕ) : ℕ := n.choose 2 / 2

/-- A123663 (offset 1): `2k - ⌈2√k⌉`. -/
noncomputable def sharedEdges (k : ℕ) : ℕ := 2 * k - ⌈2 * Real.sqrt k⌉₊

/-- Triangular numbers A000217. -/
def tri (m : ℕ) : ℕ := m * (m + 1) / 2

/-- Kagey's conjecture: for `n ≥ 3`, `a(n)` is the greatest `k ≥ 1` with
`A123663(k) < A000217(n - 2)`. -/
theorem main : ∀ n, 3 ≤ n →
    IsGreatest {k : ℕ | 1 ≤ k ∧ sharedEdges k < tri (n - 2)} (a n) := by
  sorry

end OMA.S_oeis_a011848
