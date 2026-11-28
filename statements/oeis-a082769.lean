import Mathlib

/-!
# A082769: a(n) = smallest palindromic prime that begins with A082768(n), or 0 if no such number exists.

Source: https://oeis.org/A082769
Credit: @Solfanbtc

Conjecture (OEIS A082769): no entry is zero, i.e. every number m whose first decimal digit is 1, 3, 7
or 9 (the terms of A082768) is the beginning of some palindromic prime.

Conventions: "p begins with m" means that the decimal digit string of m (most significant digit
first) is a prefix of that of p (p = m allowed, e.g. a(2) = 3). With Mathlib's little-endian
`Nat.digits`, the most-significant-first string is the reverse. A palindrome is a number whose
digit list equals its reverse. Checked against the data: the least such primes for m = 1, 3, 7, 9,
10, 11, 12, ... are 11, 3, 7, 919, 101, 11, 12421, ... as listed.
-/

namespace OMA.S_oeis_a082769

/-- `x` is a decimal palindrome. -/
def IsPal (x : ℕ) : Prop := (Nat.digits 10 x).reverse = Nat.digits 10 x

theorem main : ∀ m : ℕ, 1 ≤ m →
    (∃ d ∈ ({1, 3, 7, 9} : Finset ℕ), (Nat.digits 10 m).getLast? = some d) →
    ∃ p : ℕ, p.Prime ∧ IsPal p ∧ (Nat.digits 10 m).reverse <+: (Nat.digits 10 p).reverse := by
  sorry

end OMA.S_oeis_a082769
