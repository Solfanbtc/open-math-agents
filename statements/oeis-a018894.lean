import Mathlib

/-!
# A018894: Numbers k such that sigma(k)/phi(k) sets a new record.

Source: https://oeis.org/A018894
Credit: @Solfanbtc

Two conjectures of David A. Corneth (Sep 10 2020, in the entry):
1. "These 466 terms are the terms <= 10^75": the terms found by his search (assuming a bound on
   the LCM of the terms) are all the terms up to 10^75. The 466 terms themselves are only in an
   attached file, not in the entry; we state the conjecture as: there are exactly 466 terms
   ≤ 10^75. (This is what the conjecture says about the count; together with the attached
   list of 466 values, each of which is a term, it is equivalent to the conjecture.)
2. "For all terms t > 1 there exists a p | t such that t/p is a term" (verified by Corneth for
   the 240 terms 1 < t ≤ 10^40). In context p is a prime divisor (Corneth's search multiplies
   terms by primes); we state it with p prime. (Checked with python3 for all terms ≤ 2·10^5.)
`main` is the conjunction.

Conventions.
* k ≥ 1 is a term iff σ(k)/φ(k) > σ(j)/φ(j) for every 1 ≤ j < k (strict record, the usual
  OEIS convention; this reproduces the data 1, 2, 4, 6, 12, 24, 30, 60, 120, 180, 210, ...;
  note 3 is not a term since σ(3)/φ(3) = 2 < 3 = σ(2)/φ(2)). Ratios are compared in ℚ.
-/

namespace OMA.S_oeis_a018894

/-- σ(k)/φ(k) as a rational number. -/
def ratio (k : ℕ) : ℚ := (ArithmeticFunction.sigma 1 k : ℚ) / (Nat.totient k : ℚ)

/-- k is a term of A018894: σ(k)/φ(k) sets a new record. -/
def IsTerm (k : ℕ) : Prop := 1 ≤ k ∧ ∀ j : ℕ, 1 ≤ j → j < k → ratio j < ratio k

theorem main :
    Nat.card {k : ℕ // IsTerm k ∧ k ≤ 10 ^ 75} = 466 ∧
    ∀ t : ℕ, IsTerm t → 1 < t → ∃ p : ℕ, p.Prime ∧ p ∣ t ∧ IsTerm (t / p) := by
  sorry

end OMA.S_oeis_a018894
