import Mathlib

/-!
# A093894: Composite members of A093893.

Source: https://oeis.org/A093894
Credit: @Solfanbtc

Conjecture (Adam M. Kalman, Nov 11 2004, comment in A093894): this sequence is infinite.

A093893 consists of the numbers `n` such that every sum of two or more (distinct) divisors of
`n` is composite; A093894 lists its composite members (49, 87, 91, 121, 133, ...).

Formalization.
* "A sum of two or more divisors" is the sum of a subset `s` of `n.divisors` with at least two
  elements (distinct divisors, as in the Mathematica programs, which sum subsets of
  `Divisors[n]`).
* Such a sum is at least `1 + 2 = 3`, so "composite" is the same as "not prime" for it.
* "Composite" for `n` itself: `1 < n` and `n` not prime.

Checked with python3: these definitions give exactly the listed %S/%T/%U terms up to 961.
-/

namespace OMA.S_oeis_a093894

/-- A093893: every sum of two or more distinct divisors of `n` is composite. -/
def AllDivisorSumsComposite (n : ℕ) : Prop :=
  ∀ s ⊆ n.divisors, 2 ≤ s.card → ¬ (∑ d ∈ s, d).Prime

/-- A093894 (composite members of A093893) is infinite. -/
theorem main : {n : ℕ | 1 < n ∧ ¬ n.Prime ∧ AllDivisorSumsComposite n}.Infinite := by
  sorry

end OMA.S_oeis_a093894
