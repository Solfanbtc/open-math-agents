import Mathlib

/-!
# A108219: consecutive n whose sums of prime factors are both golden semiprimes

Source: https://oeis.org/A108219 (with https://oeis.org/A108540 and https://oeis.org/A001414)
A001414: `sopfr(n)`, the sum of the primes dividing `n`, with repetition. A108540: golden
semiprimes, `p*q` with primes `p < q` and `|p φ - q| < 1`, `φ = (1 + √5)/2` (6, 15, 77, 187, ...).
A108219 lists the `n` with `sopfr(n)` a golden semiprime (8, 9, 26, 44, ...). The entry's comment:
"Numbers n such that A001414(n) and A001414(n+1) are both golden semiprimes: 8, 125, 153759,
247455, 678807, 1243499, 1243500, ... Conjecture: this subsequence is infinite."

We state: there are infinitely many `n` such that `sopfr(n)` and `sopfr(n+1)` are both golden
semiprimes.
Conventions. The two primes are distinct (`p < q`), as in the entry's Mathematica `goldQ`
(squarefree with two prime factors, the larger one `q` within 1 of `φ` times the smaller);
`p = q` could never satisfy `|p φ - q| < 1` anyway, since `p(φ - 1) ≥ 2(φ - 1) > 1`.
Checked with python3 (exact integer comparison): the definition gives exactly the 46 listed terms
below 7500, and the `n < 1300000` with both `sopfr(n)`, `sopfr(n+1)` golden semiprimes are
exactly 8, 125, 153759, 247455, 678807, 1243499, 1243500.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a108219

/-- A001414: the sum of the prime factors of `n`, with repetition. -/
def sopfr (n : ℕ) : ℕ := n.primeFactorsList.sum

/-- A108540: `m = p q` with primes `p < q` and `|p φ - q| < 1`. -/
def IsGoldenSemiprime (m : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ m = p * q ∧ |(p : ℝ) * Real.goldenRatio - q| < 1

theorem main :
    {n : ℕ | IsGoldenSemiprime (sopfr n) ∧ IsGoldenSemiprime (sopfr (n + 1))}.Infinite := by
  sorry

end OMA.S_oeis_a108219
