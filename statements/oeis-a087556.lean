import Mathlib

/-!
# A087556: smallest prime that is the concatenation of two numbers whose sum is n.

Source: https://oeis.org/A087556
Credit: @Solfanbtc

For `n ≥ 2`, A087556(n) is the smallest prime of the form `x ‖ y` (decimal concatenation) with
positive integers `x + y = n` (ordered: for `n = 7` the candidates are `16, 61, 25, 52, 34, 43`
and `a(7) = 43`), or `0` if there is none. `a(3k) = 0`, since the digit sum of `x ‖ y` is
`≡ x + y = 3k (mod 3)`. (Zero parts are excluded: `0 ‖ 3 = 3` would make `a(3)` nonzero.)
Here `x ‖ y = x * 10^(number of digits of y) + y`.

Conjecture (entry): no other term is zero, i.e. for every `n ≥ 2` with `3 ∤ n` some
concatenation `x ‖ (n - x)`, `1 ≤ x < n`, is prime.

WARNING, the conjecture appears to be FALSE. With python3 (deterministic Miller-Rabin, and
again with plain trial division) the definition reproduces the 44 listed terms, but for
`n = 4477` and `n = 5698` (both `≡ 1 mod 3`) none of the `n - 1` concatenations is prime. These
are the only such `n ≤ 20000`. So `OMA.disproof` should be provable by exhibiting `n = 4477`
and checking the 4476 numbers `x ‖ (4477 - x)` (between `14476` and `34771000`).
-/

namespace OMA.S_oeis_a087556

/-- Decimal concatenation `x ‖ y` (for `y ≥ 1`). -/
def cat (x y : ℕ) : ℕ := x * 10 ^ (Nat.digits 10 y).length + y

/-- The conjecture (apparently false, see above): for `n ≥ 2` not divisible by 3, some
`x ‖ (n - x)` with `1 ≤ x < n` is prime. -/
theorem main : ∀ n : ℕ, 2 ≤ n → ¬ 3 ∣ n → ∃ x : ℕ, 1 ≤ x ∧ x < n ∧ (cat x (n - x)).Prime := by
  sorry

end OMA.S_oeis_a087556
