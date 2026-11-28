import Mathlib

/-!
# A083396: Least n such that n and 2k+n are both brilliant numbers.

Source: https://oeis.org/A083396 (brilliant numbers: A078972)
Credit: @Solfanbtc

A brilliant number (A078972) is a semiprime `p q` (`p, q` primes, possibly equal) whose two prime
factors have the same number of decimal digits: 4, 6, 9, 10, 14, 15, 21, 25, 35, 49, 121, ...
A083396(k) is the least `n` such that `n` and `n + 2k` are both brilliant: 4, 6, 4, 6, 4, 9, ...

Conjecture (entry): for any `k ≥ 1` there is a brilliant constellation `{n, n + 2k}`, i.e. some
`n` with `n` and `n + 2k` both brilliant (checked there for all `k ≤ 5000`).

Sanity check (python): the definition reproduces all 40 listed terms, and a witness exists for
every `k ≤ 3000`.
-/

namespace OMA.S_oeis_a083396

/-- `n` is a brilliant number. -/
def IsBrilliant (n : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q ∧ (Nat.digits 10 p).length = (Nat.digits 10 q).length

/-- The conjecture: every even gap `2k`, `k ≥ 1`, occurs between two brilliant numbers. -/
theorem main : ∀ k : ℕ, 1 ≤ k → ∃ n : ℕ, IsBrilliant n ∧ IsBrilliant (n + 2 * k) := by
  sorry

end OMA.S_oeis_a083396
