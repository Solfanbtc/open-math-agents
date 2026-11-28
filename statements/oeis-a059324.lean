import Mathlib

/-!
# A059324: Numbers n such that 6n + 5 is composite.

Source: https://oeis.org/A059324
Credit: @Solfanbtc

Conjecture (Philippe Lallouet, Mar 20 2008, in the entry): "There exists no pair of primes
(p, q > p^2) such that q - p^2 = 6*n - 4 (see A138479)", for n in this sequence. Read as a
characterization of the sequence (A138479 records the least such p when it exists): for n ≥ 1,
6n + 5 is composite iff there are no primes p, q with q > p^2 and q - p^2 = 6n - 4.

Conventions.
* n ranges over positive integers (6n - 4 ≥ 2); 6n + 5 ≥ 11 > 1, so "composite" is "not
  prime".
* Remark (not used in the statement): for p = 3 the candidate is q = 6n + 5; for p ≠ 3,
  p^2 + 6n - 4 is divisible by 3 (p = 2 gives 6n), so the claim is elementary, but it is
  stated as the source gives it.
-/

namespace OMA.S_oeis_a059324

theorem main : ∀ n : ℕ, 1 ≤ n →
    (¬ (6 * n + 5).Prime ↔
      ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ^ 2 < q ∧ q - p ^ 2 = 6 * n - 4) := by
  sorry

end OMA.S_oeis_a059324
