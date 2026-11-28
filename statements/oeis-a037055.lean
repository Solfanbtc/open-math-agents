import Mathlib

/-!
# A037055: Smallest prime containing exactly n 1's.

Source: https://oeis.org/A037055
Credit: @Solfanbtc

Conjecture (Robert G. Wilson v, Jul 04 2003, in the entry): for n > 1, A037055 is identical to
A084673, i.e. A037055(n) = A084673(n) for every n ≥ 2, where A037055(n) (offset 0) is the
smallest prime containing exactly n 1's and A084673(n) (offset 1) is the smallest prime in
which a digit appears n times.

Conventions.
* Decimal digits via `Nat.digits 10`; "contains exactly n 1's" = the digit 1 occurs exactly n
  times. "A digit appears n times" = some digit d ≤ 9 occurs exactly n times (A084673(1) = 2,
  A084673(2) = 11, A084673(3) = 1117, matching its data; at n = 1 the two sequences differ:
  A037055(1) = 13 but A084673(1) = 2, hence "n > 1").
* Both sequences are infinite in the OEIS, so the statement includes that both minima exist:
  for n ≥ 2 there is a prime p which is the least prime with exactly n 1's and also the least
  prime in which some digit occurs exactly n times. (python3: both minima agree for
  n = 2..7: 11, 1117, 10111, 101111, 1111151, 11110111.)
-/

namespace OMA.S_oeis_a037055

/-- Number of occurrences of the digit d in the decimal expansion of p. -/
def digitCount (d p : ℕ) : ℕ := (Nat.digits 10 p).count d

theorem main : ∀ n : ℕ, 2 ≤ n →
    ∃ p : ℕ, IsLeast {q : ℕ | q.Prime ∧ digitCount 1 q = n} p ∧
      IsLeast {q : ℕ | q.Prime ∧ ∃ d : ℕ, d < 10 ∧ digitCount d q = n} p := by
  sorry

end OMA.S_oeis_a037055
