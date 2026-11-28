import Mathlib

/-!
# A071052: Number of 0's in n-th row of triangle in A071036 (cellular automaton "Rule 150").

Source: https://oeis.org/A071052
Credit: @Solfanbtc

A071036 is the triangle of successive states of the elementary cellular automaton "Rule 150"
started from a single ON cell: under Rule 150 each cell becomes the XOR of itself and its two
neighbours. After `n` steps the cells that can be ON are those at positions `-n, …, n`, so row `n`
of the triangle has length `2n + 1` and consists of the states of the cells at positions
`-n ≤ i ≤ n`. (Equivalently, row `n` lists the coefficients of `(x^2 + x + 1)^n` mod 2.)

`a n` (A071052) is the number of cells in `-n ≤ i ≤ n` that are OFF after `n` steps.

The conjecture (Ralf Stephan, Mar 03 2004, in the %F line) is `a(2n) = a(n) + 2n` for all `n`
(offset 0, so `n` ranges over all natural numbers).
-/

namespace OMA.S_oeis_a071052

/-- The state of the Rule 150 cellular automaton after `n` steps, started from a single ON cell
at position `0`: cell `i` becomes the XOR of cells `i - 1`, `i`, `i + 1`. -/
def rule150 : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | n + 1, i => xor (xor (rule150 n (i - 1)) (rule150 n i)) (rule150 n (i + 1))

/-- A071052: the number of 0's (OFF cells) in row `n` of A071036, i.e. among positions
`-n ≤ i ≤ n` after `n` steps. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (2 * n + 1)).filter (fun k : ℕ => rule150 n ((k : ℤ) - (n : ℤ)) = false)).card

/-- Conjecture (Ralf Stephan, 2004): `a(2n) = a(n) + 2n`. -/
theorem main : ∀ n : ℕ, a (2 * n) = a n + 2 * n := by
  sorry

end OMA.S_oeis_a071052
