import Mathlib

/-!
# A104638: Number of odd digits in n-th prime.

Source: https://oeis.org/A104638
Credit: @Solfanbtc

Comment (Robert Israel, Jan 12 2016): "For any N, the asymptotic density of terms >= N is 1.
On the other hand, a(n) = 2 if prime(n) is in A159352, which is conjectured to be infinite."

The open claim in this comment is the conjecture that A159352 is infinite. A159352 lists the
primes of the form "1 [0]_n 3", i.e. a 1, then n ≥ 0 zeros, then a 3: the numbers
`10^k + 3` with `k ≥ 1` (k = n + 1); its data 13, 103, 100003, 1000003, ... are the primes
`10^k + 3` for k = 1, 2, 5, 6, 11, 17, 18, 39, 56 (python3). Each of them has exactly two odd
digits, so A104638 takes the value 2 at infinitely many indices if the conjecture holds.

Statement: there are infinitely many primes of the form `10^k + 3`, `k ≥ 1`.
(The first claim of the comment, density 1 of the terms ≥ N, is presented in the entry as a
fact, not as a conjecture, and is not part of this statement.)
-/

namespace OMA.S_oeis_a104638

theorem main : {p : ℕ | p.Prime ∧ ∃ k : ℕ, 1 ≤ k ∧ p = 10 ^ k + 3}.Infinite := by
  sorry

end OMA.S_oeis_a104638
