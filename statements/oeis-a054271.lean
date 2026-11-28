import Mathlib

/-!
# A054271: Difference between prime(n)^2 and the previous prime.

Source: https://oeis.org/A054271
Credit: @Solfanbtc

Conjecture (Jean-Christophe Hervé, OEIS A054271, comment, Oct 22 2013): the terms are even
except the first, even integers of the form 6k+4 never appear, and "every other even integer
appears in the sequence an infinite number of times".

Minimal fix: the conjecture fails as literally stated for even perfect squares d = m^2 with
d ≢ 4 (mod 6), such as 36, 144, 324: p^2 - m^2 = (p - m)(p + m) is prime only if p = m + 1, so
such a d occurs for at most one prime p, never infinitely often (in Python, 36 and 144 never
occur for p < 6000; 36 is the only even d < 60, d ≢ 4 mod 6, that does not occur). We state the
conjecture for every even d > 0 with d ≢ 4 (mod 6) that is not a perfect square.

Conventions:
* a(n) = prime(n)^2 - precprime(prime(n)^2), with precprime(x) the largest prime < x. "d appears
  infinitely often" is stated over the primes p = prime(n), which correspond to the indices n
  one to one: there are infinitely many primes p with d < p^2, p^2 - d prime, and no prime
  strictly between p^2 - d and p^2.
* Checked in Python: this reproduces every term of %S, %T, %U, and for p < 20000 every value
  after the first is even and ≢ 4 (mod 6).
-/

namespace OMA.S_oeis_a054271

/-- `p^2 - d` is the prime preceding `p^2`. -/
def PrevPrimeGap (p d : ℕ) : Prop :=
  d < p ^ 2 ∧ (p ^ 2 - d).Prime ∧ ∀ q ∈ Finset.Ioo (p ^ 2 - d) (p ^ 2), ¬ q.Prime

/-- Hervé's conjecture (with even perfect squares excluded): every even `d > 0` with
`d ≢ 4 (mod 6)` that is not a square is `prime(n)^2 - precprime(prime(n)^2)` for infinitely
many `n`. -/
theorem main :
    ∀ d : ℕ, 0 < d → Even d → d % 6 ≠ 4 → ¬ IsSquare d →
      {p : ℕ | p.Prime ∧ PrevPrimeGap p d}.Infinite := by
  sorry

end OMA.S_oeis_a054271
