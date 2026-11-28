import Mathlib

/-!
# A088258: Factorials F which have at least one prime neighbor, i.e., F+1 or F-1 or both are primes.

Source: https://oeis.org/A088258
Credit: @Solfanbtc

The entry's comment reads: "Conjecture: sequence is infinite. But there are finitely many members
which are sandwiched between twin primes."

The first half (infinitely many factorials `F` with `F - 1` or `F + 1` prime) is equivalent to the
infinitude of factorial primes, already stated upstream as
`FactorialPrime.infinitely_many_factorial_primes` (FormalConjectures/Wikipedia/FactorialPrime.lean),
so only the second half is stated here: there are only finitely many factorials `F = n!` with both
`F - 1` and `F + 1` prime. (Known example: `3! = 6`, between 5 and 7; `0! = 1! = 1` and `2! = 2`
do not qualify since `0` and `1` are not prime. python3: `n = 3` is the only `n ≤ 150` with both
`n! - 1` and `n! + 1` prime; the indices with at least one prime neighbor up to 39 are
0, 1, 2, 3, 4, 6, 7, 11, 12, 14, 27, 30, 32, 33, 37, 38, matching A088412 (which starts at 1).)
-/

namespace OMA.S_oeis_a088258

/-- The members of A088258 sandwiched between twin primes: factorials `F` with `F - 1` and `F + 1`
both prime. -/
def S : Set ℕ :=
  {F : ℕ | (∃ n : ℕ, F = n.factorial) ∧ (F - 1).Prime ∧ (F + 1).Prime}

/-- Conjecture (OEIS A088258): only finitely many factorials lie between twin primes. -/
theorem main : S.Finite := by
  sorry

end OMA.S_oeis_a088258
