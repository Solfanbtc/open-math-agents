import Mathlib

/-!
# A089574: Column 4 of an array closely related to A083480. (Both arrays have shape sequence A083479).

Source: https://oeis.org/A089574
Credit: @Solfanbtc

Conjecture (R. J. Mathar, Jun 26 2010, comment in A089574): the terms of A089574 are the
first differences of the conjectured polynomial formula for A006468, i.e. for `n ≥ 1`
`a(n) = P(n) - P(n-1)` with
`P(n) = n (n+1) (n+2) (2 n^3 + 33 n^2 + 142 n + 123) / 360`
(Plouffe's formula for A006468, conjectured in 1992 and proved by Andrew Howroyd, Apr 02 2021;
only the polynomial enters this statement). Equivalently
`a(n) = n (n+1) (4 n^3 + 51 n^2 + 159 n + 86) / 120`.

The array. A089574 is column 4 of the array in its %e lines, whose columns 1, 2, 3, 4 are
A000124, A000330, A086602, A089574; A105552 identifies this array: its entry `T(n, k)` is the
number of compositions `c` of `n` with `largest_part(c) + length(c) = k + 1`, and its
(sub)diagonals in order are A000124, A000330, A086602, A089574, ... . Column 4 is the diagonal
`T(k + 3, k)`, which is `0` for `k ≤ 4` and starts at `k = 5` with `T(8, 5) = 5`, so
`a(n) = T(n + 7, n + 4)` for `n ≥ 1` (offset 1, as in OEIS).

Checked with python3: `T(n + 7, n + 4)` reproduces all 33 listed %S/%T/%U terms
(5, 32, 113, ..., 1913197), and the difference formula agrees with them.
-/

namespace OMA.S_oeis_a089574

/-- Largest part of a composition (`0` for the empty composition of `0`). -/
def largestPart {n : ℕ} (c : Composition n) : ℕ := c.blocks.foldr max 0

/-- A105552: `T n k` is the number of compositions `c` of `n` with
`largestPart c + c.length = k + 1`. -/
def T (n k : ℕ) : ℕ :=
  (Finset.univ.filter (fun c : Composition n => largestPart c + c.length = k + 1)).card

/-- A089574 (offset 1): `a n = T (n + 7) (n + 4)`, column 4 of the array. -/
def a (n : ℕ) : ℕ := T (n + 7) (n + 4)

/-- Plouffe's polynomial formula for A006468. -/
def P (x : ℚ) : ℚ := x * (x + 1) * (x + 2) * (2 * x ^ 3 + 33 * x ^ 2 + 142 * x + 123) / 360

/-- Mathar's conjecture: A089574 is the sequence of first differences of the polynomial
formula for A006468. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = P n - P (n - 1) := by
  sorry

end OMA.S_oeis_a089574
