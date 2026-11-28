import Mathlib

/-!
# A080651: Numbers n such that n and Fibonacci(n) have the same number of divisors.

Source: https://oeis.org/A080651
Credit: @Solfanbtc

A080651 (offset 1) lists the positive `m` with `d(m) = d(F(m))`, `d` the number of divisors;
A001605 (offset 1) lists the `m` with `F(m)` prime. With `Nat.nth` (0-indexed),
`A080651(n) = Nat.nth P (n - 1)` and `A001605(k) = Nat.nth Q (k - 1)`.
We checked that `P` below 131 is 1, 3, 5, 6, 7, 8, 10, 11, 13, 14, 17, 22, 23, 26, 29, 34, 43,
47, 83, 94 (the first 20 terms of %S) and that `Q` starts 3, 4, 5, 7, ..., 83, 131, 137
(so `A001605(13) = 131 = A080651(21)`).

Conjecture (Chai Wah Wu, 2019): `A080651(n) = A001605(n - 8)` for `n ≥ 21`.
-/

namespace OMA.S_oeis_a080651

/-- The terms of A080651: positive `m` with as many divisors as `F(m)`. -/
def P (m : ℕ) : Prop := 0 < m ∧ m.divisors.card = (Nat.fib m).divisors.card

/-- The terms of A001605: indices of prime Fibonacci numbers. -/
def Q (m : ℕ) : Prop := (Nat.fib m).Prime

/-- Wu's conjecture: `A080651(n) = A001605(n - 8)` for `n ≥ 21`. -/
theorem main : ∀ n : ℕ, 21 ≤ n → Nat.nth P (n - 1) = Nat.nth Q (n - 8 - 1) := by
  sorry

end OMA.S_oeis_a080651
