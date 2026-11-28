import Mathlib

/-!
# A126016: Numbers whose aliquot sequence does not terminate in 1.

Source: https://oeis.org/A126016
Credit: @Solfanbtc

Claim (Nathaniel J. Strout, Nov 25 2018, comment in A126016): "For additional terms, if the
Goldbach Conjecture is assumed, take any odd term, subtract 1, and find two distinct primes that
sum to it. For some numbers there will not be any pair of distinct primes. Multiply the two
primes and the product is an element of the sequence."

Formalization.
* `s(n) = σ(n) - n`, the sum of the proper divisors of `n`; the aliquot sequence of `n` is
  `n, s(n), s(s(n)), ...`, and it terminates in 1 if some iterate equals 1 (primes reach 1 in
  one step; `1` itself is counted as terminating, as in the Mathematica program).
* A126016 is the set of `n ≥ 1` whose aliquot sequence never reaches 1.
* The claim, for the pairs that exist: if `t` is an odd term and `t - 1 = p + q` with distinct
  primes `p, q`, then `p q` is a term. Goldbach's conjecture only enters to guarantee that
  such `p, q` exist, which is not part of this statement.

Status: elementary, since `s(p q) = 1 + p + q = t`, so the aliquot sequence of `p q` continues
with that of `t`. Stated as posed.

Checked with python3: from the term `25`, `24 = 5 + 19 = 7 + 17 = 11 + 13` gives the listed
terms `95, 119, 143` (`s = 25` for each).
-/

namespace OMA.S_oeis_a126016

/-- The sum of the proper divisors of `n`. -/
def s (n : ℕ) : ℕ := ∑ d ∈ n.properDivisors, d

/-- `n` is in A126016: `n ≥ 1` and the aliquot sequence of `n` never reaches 1. -/
def InSeq (n : ℕ) : Prop := 1 ≤ n ∧ ∀ k : ℕ, s^[k] n ≠ 1

/-- Strout's construction: for an odd term `t` and distinct primes `p, q` with
`p + q = t - 1`, the product `p q` is a term. -/
theorem main : ∀ t : ℕ, InSeq t → Odd t → ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
    p + q = t - 1 → InSeq (p * q) := by
  sorry

end OMA.S_oeis_a126016
