import Mathlib

/-!
# A107740: Number of numbers m such that prime(n) = m + (digit sum of m).

Source: https://oeis.org/A107740
Credit: @Solfanbtc

`a(n)` (offset 1) is the number of `m` with `m + s(m) = prime(n)`, `s` the decimal digit sum
(A230093 evaluated at primes): 1, 0, 0, 0, 1, 1, ...; e.g. `prime(26) = 101 = 91 + 10 = 100 + 1`,
so `a(26) = 2`. Any such `m` is below `prime(n)`, so counting `m < prime(n)` loses nothing.

Conjecture (R. Zumkeller, in the entry, after checking `a(n) ≤ 2` for `n ≤ 10^5`): the sequence
is bounded. M. F. Hasler (2018, in the entry) would rather conjecture the opposite; this is open.
-/

namespace OMA.S_oeis_a107740

/-- A107740(n): the number of `m` with `m + s(m) = prime(n)` (`prime(n) = Nat.nth Nat.Prime (n-1)`). -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.range (Nat.nth Nat.Prime (n - 1))).filter
    fun m => m + (Nat.digits 10 m).sum = Nat.nth Nat.Prime (n - 1)).card

/-- Conjecture: A107740 is bounded. -/
theorem main : ∃ B : ℕ, ∀ n : ℕ, 1 ≤ n → a n ≤ B := by
  sorry

end OMA.S_oeis_a107740
