import Mathlib

/-!
# A308247: a(n) is the least integer not the difference of two prime(n)-smooth numbers.

Source: https://oeis.org/A308247
Credit: @Solfanbtc

Conjecture (OEIS A308247, comment): the next few terms are conjectured to be
158857, 681179, 2516509, 10772123, 51292187, 186323681 (if they were not, they would
provide examples of ABC-triples with quality greater than 2).

The known terms 5, 41, 281, 1849, 9007, 35803 are a(1), ..., a(6), so the conjectured values
are a(7), ..., a(12), for prime(7), ..., prime(12) = 17, 19, 23, 29, 31, 37.

Conventions:
* A prime(n)-smooth number is a positive integer with no prime factor greater than
  prime(n); in Mathlib this is `Nat.smoothNumbers (prime(n) + 1)` (prime factors `< prime(n)+1`).
* a(n) is the least positive integer m such that there are no smooth a, b with a - b = m,
  i.e. a = b + m. (Checked in Python with a bounded search: this gives 5, 41, 281 for
  primes up to 2, 3, 5.)
* The statement asserts all six conjectured values.
-/

namespace OMA.S_oeis_a308247

/-- `m` is a difference of two `p`-smooth numbers. -/
def IsSmoothDiff (p m : ℕ) : Prop :=
  ∃ a ∈ Nat.smoothNumbers (p + 1), ∃ b ∈ Nat.smoothNumbers (p + 1), a = b + m

/-- `v` is the least positive integer that is not a difference of two `p`-smooth numbers. -/
def IsLeastNonDiff (p v : ℕ) : Prop :=
  IsLeast {m : ℕ | 0 < m ∧ ¬ IsSmoothDiff p m} v

/-- Conjecture: a(7), ..., a(12) are 158857, 681179, 2516509, 10772123, 51292187, 186323681. -/
theorem main :
    IsLeastNonDiff 17 158857 ∧ IsLeastNonDiff 19 681179 ∧ IsLeastNonDiff 23 2516509 ∧
    IsLeastNonDiff 29 10772123 ∧ IsLeastNonDiff 31 51292187 ∧
    IsLeastNonDiff 37 186323681 := by
  sorry

end OMA.S_oeis_a308247
