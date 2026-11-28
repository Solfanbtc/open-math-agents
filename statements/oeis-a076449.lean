import Mathlib

/-!
# A076449: for every n some number's digits form exactly n different primes

Source: https://oeis.org/A076449
Credit: @Solfanbtc

A076449 (offset 0): the least number whose digits can be used to form exactly `n` different
primes (not necessarily using all digits); `a(n) = min { m : A039993(m) = n }`.
Data 1, 2, 25, 13, 37, 107, 127, 113, 167, 1027, 179, …; e.g. `a(10) = 179`, harboring the ten
primes 7, 17, 19, 71, 79, 97, 179, 197, 719, 971.

Conjecture (M. Keith, in the entry): "a(n) always exists" (checked by him for `n ≤ 66`), i.e.
for every `n` some `m ≥ 1` has exactly `n` such primes.

Definition of A039993(m). A prime is formed from digits of `m` iff the multiset of its decimal
digits is contained in the multiset of digits of `m` (an arrangement with leading zeros is just a
smaller number whose digits again form a sub-multiset, so it adds no new primes). Checked with
python3: with this definition the least `m` with exactly `n` primes reproduces the 17 listed terms.
-/

namespace OMA.S_oeis_a076449

/-- A039993: the number of primes whose decimal digits form a sub-multiset of those of `m`. -/
noncomputable def numPrimes (m : ℕ) : ℕ :=
  {p : ℕ | p.Prime ∧ (Nat.digits 10 p : Multiset ℕ) ≤ (Nat.digits 10 m : Multiset ℕ)}.ncard

/-- Keith's conjecture: every `n` is the number of primes formed from the digits of some `m`. -/
theorem main : ∀ n : ℕ, ∃ m : ℕ, 1 ≤ m ∧ numPrimes m = n := by
  sorry

end OMA.S_oeis_a076449
