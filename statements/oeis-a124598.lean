import Mathlib

/-!
# A124598: Primes p of the form k^2+s where k > 1 and 1 <= s < (k+1)^2, such that q = k^4+s is prime and larger than p.

Source: https://oeis.org/A124598
Credit: @Solfanbtc

A124598: "The terms of this sequence illustrate a special case of the conjecture from A126769."
That conjecture (Tomas Xordan, A126769, as rephrased there by M. F. Hasler, May 23 2018):
every prime `q > 3` can be written in a nontrivial way as the sum of two or more squares,
`q = Sum_i k_i^2`, such that the sum of the fourth powers of the squared numbers,
`p = Sum_i k_i^4`, is again prime. (A124598 is the case of one square `k^2`, `k > 1`, plus
`s` squares `1^2`.)

Formalization.
* The squares are those of positive integers `k_i ≥ 1`, with repetitions (a list); "two or more
  squares" is `length ≥ 2`.
* "Nontrivial": not all `k_i` equal to 1. If every `k_i = 1` then `Sum k_i^4 = Sum k_i^2 = q`
  is trivially prime, so the conjecture is only meaningful with some `k_i ≥ 2`; this is the
  reading of A126769 ("the case where only one of the squares is larger than 1 and all other
  terms are equal to 1" is its easy case).

Checked with python3: every prime `5 ≤ q < 3000` has such a representation (e.g.
`5 = 2^2 + 1^2`, `2^4 + 1 = 17`; `11 = 3^2 + 1^2 + 1^2`, `3^4 + 2 = 83`).
-/

namespace OMA.S_oeis_a124598

/-- Xordan's conjecture (A126769): every prime `q > 3` is a sum of at least two positive
squares `k_i^2`, not all with `k_i = 1`, whose fourth powers `k_i^4` sum to a prime. -/
theorem main : ∀ q : ℕ, q.Prime → 3 < q →
    ∃ l : List ℕ, 2 ≤ l.length ∧ (∀ k ∈ l, 1 ≤ k) ∧ (∃ k ∈ l, 2 ≤ k) ∧
      (l.map (· ^ 2)).sum = q ∧ ((l.map (· ^ 4)).sum).Prime := by
  sorry

end OMA.S_oeis_a124598
