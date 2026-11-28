import Mathlib

/-!
# A155860: Number of ways to write 2n-1 as p + 2^x + 3*2^y with p an odd prime and x,y positive integers.

Source: https://oeis.org/A155860
Credit: @Solfanbtc

Conjecture (Zhi-Wei Sun, Jan 21 2009, in the entry): a(n) > 0 for n = 6, 7, ...; in other words,
any odd integer m > 10 can be written as the sum of an odd prime, a positive power of 2 and three
times a positive power of 2. (Verified for odd m < 10^10 by Greathouse.)

Conventions.
* Stated in the "in other words" form: for every odd m > 10 there are an odd prime p and
  positive integers x, y with m = p + 2^x + 3·2^y. This is exactly a(n) > 0 for n ≥ 6 with
  m = 2n - 1. The bound m > 10 is sharp: the data give a(1) = ... = a(5) = 0
  (m = 1, 3, 5, 7, 9) and a(6) = 1 (11 = 3 + 2 + 6).
-/

namespace OMA.S_oeis_a155860

theorem main : ∀ m : ℕ, Odd m → 10 < m →
    ∃ p x y : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ x ∧ 1 ≤ y ∧ m = p + 2 ^ x + 3 * 2 ^ y := by
  sorry

end OMA.S_oeis_a155860
