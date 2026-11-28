import Mathlib

/-!
# A083660: least m with the concatenation n, m, n-1, m, …, 2, m, 1 prime.

Source: https://oeis.org/A083660
Credit: @Solfanbtc

For `n ≥ 2`, A083660(n) is the smallest nonnegative integer `m` such that the base-10
concatenation of `n, m, n-1, m, …, 2, m, 1` (the integers from `n` down to `1` with `m` inserted
between consecutive ones) is prime. For example, `a(4) = 14` since `4143142141` is prime.
`concat` concatenates the decimal representations of a list of numbers (`0` written as the one
digit `0`). (The entry's Mathematica program starts its search at `m = 1`. For `m = 0` the
concatenation is never prime for `2 ≤ n ≤ 70`, checked with python3, so the data is the same.)

Firoozbakht's conjecture (from the entry): for every `n > 1`, `a(n)` exists and is less than
`n^2`, i.e. some `m < n^2` makes the concatenation prime. Checked with python3 (Miller-Rabin):
the definition reproduces the 69 listed terms `n = 2..70`, all below `n^2`.
-/

namespace OMA.S_oeis_a083660

/-- Number of decimal digits of `y` (`1` for `y = 0`). -/
def ndig (y : ℕ) : ℕ := max 1 (Nat.digits 10 y).length

/-- Decimal concatenation of a list of numbers. -/
def concat (l : List ℕ) : ℕ := l.foldl (fun acc y => acc * 10 ^ ndig y + y) 0

/-- The list `n, m, n-1, m, …, 2, m, 1`. -/
def interleave (n m : ℕ) : List ℕ :=
  ((List.range (n - 1)).reverse.map (· + 2)).flatMap (fun i => [i, m]) ++ [1]

/-- Firoozbakht's conjecture: for `n > 1`, some `m < n^2` makes the concatenation prime. -/
theorem main : ∀ n : ℕ, 1 < n → ∃ m : ℕ, m < n ^ 2 ∧ (concat (interleave n m)).Prime := by
  sorry

end OMA.S_oeis_a083660
