import Mathlib

/-!
# A067874: Positive integers x satisfying x^2 - D*y^2 = 1 for a unique integer D.

Source: https://oeis.org/A067874
Credit: @Solfanbtc

Conjecture (OEIS A067874, comment by Griffin N. Macris, Apr 11 2016):
All terms of A002110 > 1 are a subsequence.

A002110 is the sequence of primorials 1, 2, 6, 30, 210, ...; its terms > 1 are exactly the
numbers `primorial p` (product of the primes <= p) for p prime. The conjecture says each of
them is a term of A067874, i.e. a positive integer x for which there is exactly one integer D
such that x^2 - D*y^2 = 1 for some integer y. The definition is used as named; by the first
comment of the entry this is the same as x^2 - 1 = (x - 1)(x + 1) being squarefree, so the
conjecture says that every p# - 1 and every p# + 1 is squarefree. (x = 1 is excluded by the
definition: there y = 0 works for every D.)

Checked in Python: the definition reproduces the listed data up to 198, and (p#)^2 - 1 is
squarefree for every prime p <= 37.

Not a duplicate of `EuclidNumbers.euclid_numbers_are_square_free` upstream, which concerns
only p# + 1; this conjecture also needs p# - 1 to be squarefree.
-/

namespace OMA.S_oeis_a067874

/-- `x` is a term of A067874: there is exactly one integer `D` with `x^2 - D*y^2 = 1` for
some integer `y`. -/
def IsTerm (x : ℕ) : Prop :=
  0 < x ∧ ∃! D : ℤ, ∃ y : ℤ, (x : ℤ) ^ 2 - D * y ^ 2 = 1

/-- Conjecture: every primorial greater than 1 is a term of A067874. -/
theorem main : ∀ p : ℕ, p.Prime → IsTerm (primorial p) := by
  sorry

end OMA.S_oeis_a067874
