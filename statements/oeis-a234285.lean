import Mathlib

/-!
# A234285: Positive odd numbers n such that sigma(m) - 2m is never equal to n. Conjectural.

Source: https://oeis.org/A234285
Credit: @Solfanbtc

Conjectures (Farideh Firoozbakht, OEIS A234285, comments, Jan 12 2014):
1. "It seems that for each even number r, there exists at least one odd prime of the form
   2^k - r - 1. This means there is no even term in the sequence."
2. "Moreover I conjecture that, for each even number r, there exist infinitely many primes p of
   the form 2^k - r - 1, or equivalently, I conjecture that: For each odd number s, there exists
   infinitely many primes p of the form 2^k - s." (Special cases listed: s = 1 Mersenne primes,
   s = -1 Fermat primes, s = 3, -3, -5.)

(The numbered comments 1-3 before these, e.g. Mersenne primes not being terms, are proved in
Firoozbakht-Hasler 2010 and are not conjectures.)

Conventions:
* In conjecture 1, r ranges over the positive even numbers (the terms of the sequence are
  positive; r = 0 is covered by the prime 3 = 2^2 - 1 anyway), k over ℕ, and the prime is a
  positive odd prime p with p = 2^k - r - 1.
* In conjecture 2, s ranges over all odd integers (the special cases include negative s, and the
  stated equivalence with "each even r" uses s = r + 1 with r over all even integers). "Infinitely
  many primes of the form 2^k - s" is the infiniteness of the set of (positive) primes p with
  p = 2^k - s for some k ∈ ℕ.
* Note (checked in Python): s = 7629217 is an Erdős-type covering number: for every k,
  2^k - 7629217 is divisible by one of 3, 5, 7, 13, 17, 241 (checked for all k < 200; the
  residues of 2^k are periodic with period 24), and it is positive only for k ≥ 23, where it
  exceeds 241. So no prime has the form 2^k - 7629217, and both conjectures as stated appear to
  fail at s = 7629217, resp. r = 7629216. They are stated faithfully nonetheless.
-/

namespace OMA.S_oeis_a234285

/-- Firoozbakht's two conjectures on primes of the form `2^k - r - 1` and `2^k - s`. -/
theorem main :
    (∀ r : ℕ, 0 < r → Even r → ∃ k p : ℕ, p.Prime ∧ Odd p ∧ p + r + 1 = 2 ^ k) ∧
    (∀ s : ℤ, Odd s →
      {p : ℕ | p.Prime ∧ ∃ k : ℕ, (p : ℤ) = 2 ^ k - s}.Infinite) := by
  sorry

end OMA.S_oeis_a234285
