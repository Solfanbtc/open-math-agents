import Mathlib

/-!
# A091915: Maximum of even products of partitions of n.

Source: https://oeis.org/A091915
Credit: @Solfanbtc

`a(n)` (`n ≥ 1`) is the maximum of the products of the parts over the partitions of `n` whose
product is even (`0` if there is none, as for `n = 1`). E.g. for `n = 5` the products are
`5, 4, 6, 3, 4, 2, 1` and `a(5) = 6`.

Conjecture (Ralf Stephan, 2004): for `n > 6`, `a(n+3) = 3 a(n)`. Checked with python3: the
definition reproduces the 42 listed terms, and the recurrence holds for `7 ≤ n ≤ 39`.
-/

namespace OMA.S_oeis_a091915

/-- A091915(n): the largest even product of the parts of a partition of `n`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition n)).filter (fun p => Even p.parts.prod)).sup
    (fun p => p.parts.prod)

/-- The conjecture: `a(n+3) = 3 a(n)` for `n > 6`. -/
theorem main : ∀ n : ℕ, 6 < n → a (n + 3) = 3 * a n := by
  sorry

end OMA.S_oeis_a091915
