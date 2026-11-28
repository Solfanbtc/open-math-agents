import Mathlib

/-!
# A084189: Minimum digit out of both prime factors of the numbers in A046376.

Source: https://oeis.org/A084189
Credit: @Solfanbtc

A046376 lists the palindromes `n = p q` (base 10) with `p, q` palindromic primes (semiprime
palindromes whose two prime factors, counted with multiplicity, are palindromes). For each, the
sequence gives the least decimal digit occurring in `p` or `q`. For example `262 = 2 · 131`
gives 1, and `9 = 3 · 3` gives 3.

Conjecture (J. Earls, 2003): this minimum digit is never greater than 3. Equivalently: whenever
`p` and `q` are palindromic primes with `p q` a palindrome, some digit of `p` or of `q` is at
most 3. `main` states this. (Suggested by the JRM problem "Find a composite palindrome larger
than 343 whose prime factors are palindromes consisting of digits greater than 3". Checked with
python3: no pair among the 89 palindromic primes below 10^7 with all digits ≥ 4 has a
palindromic product.)
-/

namespace OMA.S_oeis_a084189

/-- `n` is a base-10 palindrome. -/
def IsPal (n : ℕ) : Prop := (Nat.digits 10 n).reverse = Nat.digits 10 n

theorem main :
    ∀ p q : ℕ, p.Prime → q.Prime → IsPal p → IsPal q → IsPal (p * q) →
      ∃ d ∈ Nat.digits 10 p ++ Nat.digits 10 q, d ≤ 3 := by
  sorry

end OMA.S_oeis_a084189
