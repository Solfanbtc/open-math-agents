import Mathlib

/-!
# A091592: 122 is the last n with no twin primes between n^2 and (n+1)^2

Source: https://oeis.org/A091592
Credit: @Solfanbtc

A091592: the numbers `n` such that there are no twin primes between `n^2` and `(n+1)^2`; in the
entry's precise form, no pair of twin primes `P, P + 2` with `n^2 < P < P + 2 < n^2 + 2n`.
Data 1, 9, 19, 26, 27, 30, 34, 39, 49, 53, 77, 122.

Conjecture (in the entry): "there are no further terms beyond a(12)=122" (tested to 50000 by
R. G. Wilson v, and to `10^7` by A. Wesolowski). `main` states that `122` is the greatest term.
(This would imply that there are infinitely many twin primes.) Checked with python3: the terms
below 3000 are exactly the 12 listed ones.
-/

namespace OMA.S_oeis_a091592

/-- `n` is a term: no twin primes `P, P + 2` with `n^2 < P < P + 2 < n^2 + 2n`. -/
def NoTwins (n : ℕ) : Prop :=
  ¬ ∃ P : ℕ, n ^ 2 < P ∧ P + 2 < n ^ 2 + 2 * n ∧ P.Prime ∧ (P + 2).Prime

/-- The conjecture: `122` is the last term of A091592. -/
theorem main : IsGreatest {n : ℕ | 1 ≤ n ∧ NoTwins n} 122 := by
  sorry

end OMA.S_oeis_a091592
