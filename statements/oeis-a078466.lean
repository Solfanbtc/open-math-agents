import Mathlib

/-!
# A078466: First cycle is reached under a "Collatz-Fibonacci" transform.

Source: https://oeis.org/A078466
Credit: @Solfanbtc

For `n`, let `x(1) = 1`, `x(2) = n` and, for `k ≥ 3`, `x(k) = x(k-1) + x(k-2)` if `x(k-1)` and
`x(k-2)` have opposite parities, `x(k) = |x(k-1) - x(k-2)| / 2` otherwise. `pairs n k` is
`(x(k+1), x(k+2))`; the rule only depends on this pair, so the sequence is eventually periodic
as soon as a pair repeats. The two known cycles are `(1; 1; 0)`, which contains the pair
`(1, 1)`, and `(1; 2; 3; 5)`, which contains the pair `(1, 2)`. A sequence that ends up in one of
these cycles passes through the corresponding pair, and conversely reaching that pair means
entering that cycle. A078466 lists the `n` whose sequence reaches `(1; 1; 0)`.

Conjecture (entry): for any `n` (`n ≥ 1`), `x(k)` reaches one of the two cycles `(1; 1; 0)` and
`(1; 2; 3; 5)`. Checked with python3: the definition reproduces the listed terms (`n < 170`), and
every `n ≤ 200000` reaches `(1, 1)` or `(1, 2)` within 1966 steps.
-/

namespace OMA.S_oeis_a078466

/-- One step: the next term after `a, b`. -/
def next (a b : ℕ) : ℕ :=
  if a % 2 ≠ b % 2 then a + b else (if b ≤ a then a - b else b - a) / 2

/-- `pairs n k = (x(k+1), x(k+2))` for the sequence with `x(1) = 1`, `x(2) = n`. -/
def pairs (n : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, n)
  | k + 1 => ((pairs n k).2, next (pairs n k).1 (pairs n k).2)

/-- The conjecture: every start reaches the cycle `(1; 1; 0)` or the cycle `(1; 2; 3; 5)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, pairs n k = (1, 1) ∨ pairs n k = (1, 2) := by
  sorry

end OMA.S_oeis_a078466
