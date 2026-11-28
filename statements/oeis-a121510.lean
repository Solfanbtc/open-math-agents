import Mathlib

/-!
# A121510: Conjectured to be complete list of cycle lengths for 3x+1 (or Collatz) problem.

Source: https://oeis.org/A121510
Credit: @Solfanbtc

The entry (data 1, 2, 3, 5, 18) counts cycles of the 3x+1 map over all integers: (0), (-1, -2),
(4, 2, 1), (-5, -14, -7, -20, -10) and (-17, -50, -25, -74, -37, -110, -55, -164, -82, -41,
-122, -61, -182, -91, -272, -136, -68, -34); "the generalized cycle conjecture asserts that these
are the only such cycles".

Formalization.
* The map on `ℤ`: `C x = x / 2` if `x` is even, `3x + 1` otherwise.
* `x` lies on a cycle iff `C^[k] x = x` for some `k ≥ 1`.
* Statement: the integers lying on a cycle are exactly the 29 integers of the five listed
  cycles. (That each listed tuple is a cycle is a direct check; the content is that there are
  no others. This implies that the cycle lengths are exactly 1, 2, 3, 5, 18.)
Note: this is not implied by the upstream (positive-integer) Collatz conjecture, which says
nothing about negative integers.
-/

namespace OMA.S_oeis_a121510

/-- The 3x+1 map on the integers. -/
def C (x : ℤ) : ℤ := if Even x then x / 2 else 3 * x + 1

/-- The elements of the five known cycles. -/
def known : Finset ℤ :=
  {0, -1, -2, 4, 2, 1, -5, -14, -7, -20, -10,
   -17, -50, -25, -74, -37, -110, -55, -164, -82, -41, -122, -61, -182, -91, -272, -136, -68, -34}

theorem main : ∀ x : ℤ, (∃ k : ℕ, 1 ≤ k ∧ C^[k] x = x) ↔ x ∈ known := by
  sorry

end OMA.S_oeis_a121510
