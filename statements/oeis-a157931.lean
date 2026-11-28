import Mathlib

/-!
# A157931: Numbers that are both the sum and the product of two primes.

Source: https://oeis.org/A157931
Credit: @Solfanbtc

Claim (N. J. A. Sloane, Mar 14 2009, as recorded in the entry): assuming the Goldbach conjecture,
this sequence is A001358 ∩ (A005843 ∪ A052147), i.e. the semiprimes (products of two primes)
that are even or of the form `p + 2` with `p` prime; the reason given is that an odd number `n` is
the sum of two primes iff `n - 2` is prime.

Stated as `Goldbach → {n | n is a sum of two primes ∧ n is a product of two primes} =
{n | n is a product of two primes ∧ (Even n ∨ ∃ p prime, n = p + 2)}`.

A python3 check: the two sets agree for `n ≤ 20000` (unconditionally in that range).

Conventions:
* "two primes" allows equal primes (`4 = 2 + 2 = 2 · 2`, `9 = 3 · 3`), as in the data.
* A005843 is the nonnegative even numbers, A052147 is `prime(n) + 2`.
* Goldbach's conjecture: every even integer `n > 2` is the sum of two primes.
-/

namespace OMA.S_oeis_a157931

/-- Goldbach's conjecture: every even `n > 2` is the sum of two primes. -/
def Goldbach : Prop := ∀ n : ℕ, 2 < n → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n

/-- Assuming Goldbach, A157931 = A001358 ∩ (A005843 ∪ A052147). -/
theorem main : Goldbach →
    {n : ℕ | (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q) ∧ (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q)}
      = {n : ℕ | (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q) ∧
          (Even n ∨ ∃ p : ℕ, p.Prime ∧ n = p + 2)} := by
  sorry

end OMA.S_oeis_a157931
