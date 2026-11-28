import Mathlib

/-!
# A087202: a(n) is the smallest m such that m > A037153(n) and n!+ m is prime.

Source: https://oeis.org/A087202
Credit: @Solfanbtc

A037153(n) is the least `m > 1` with `n! + m` prime, and `a(n)` is the least `m > A037153(n)`
with `n! + m` prime, i.e. the second `m > 1` with `n! + m` prime. (Both sets are nonempty, as
there are infinitely many primes.) This reproduces every term of %S, %T, %U (Python).

Conjecture (Farideh Firoozbakht, in the entry): for `n > 1`, `a(n)` is prime (compare the
conjecture that every term of A037153 is prime). `a(1) = 4` is why `n = 1` is excluded. The entry
reports it holds through 1200 terms; checked here in Python for `2 ≤ n ≤ 150`.
-/

namespace OMA.S_oeis_a087202

/-- A037153: the least `m > 1` with `n! + m` prime. -/
noncomputable def A037153 (n : ℕ) : ℕ := sInf {m : ℕ | 1 < m ∧ (n.factorial + m).Prime}

/-- A087202: the least `m > A037153(n)` with `n! + m` prime. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m : ℕ | A037153 n < m ∧ (n.factorial + m).Prime}

theorem main : ∀ n : ℕ, 1 < n → (a n).Prime := by
  sorry

end OMA.S_oeis_a087202
