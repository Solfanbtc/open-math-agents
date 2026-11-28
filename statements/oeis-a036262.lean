import Mathlib

/-!
# A036262: Array of numbers read by upward antidiagonals, arising from Gilbreath's conjecture: leading row lists the primes; the following rows give absolute values of the differences of the previous row.

Source: https://oeis.org/A036262
Credit: @Solfanbtc

Conjecture (Gilbreath): "The conjecture is that the leading term is always 1."

Formalization notes:
* Row 0 is the leading row of the array, the primes 2, 3, 5, 7, ...; row `n + 1` lists the
  absolute differences of consecutive terms of row `n`. Columns are indexed from 0, so
  `row n 0` is the leading (first) term of row `n`.
* The leading term of row 0 is the prime 2, so "the leading term is always 1" refers to the
  rows of differences, i.e. to every row `n ≥ 1` (rows 1, 2, 3, ... begin 1, 1, 1, ...).
* The same conjecture appears upstream as `Gilbreath.gilbreath_conjecture`
  (FormalConjectures/Wikipedia/Gilbreath.lean); here it is stated directly on the array.
-/

namespace OMA.S_oeis_a036262

/-- The array A036262: row 0 is the primes, row `n + 1` is the absolute differences of row `n`. -/
noncomputable def row : ℕ → ℕ → ℕ
  | 0, j => Nat.nth Nat.Prime j
  | n + 1, j => Nat.dist (row n (j + 1)) (row n j)

/-- Gilbreath's conjecture: every row after the row of primes starts with 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → row n 0 = 1 := by
  sorry

end OMA.S_oeis_a036262
