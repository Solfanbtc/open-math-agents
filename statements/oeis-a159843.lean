import Mathlib

/-!
# A159843: Sums of two rational cubes have natural density 1/2

Source: https://oeis.org/A159843
Credit: @Solfanbtc

A159843 lists the positive integers `n` that are sums of two rational cubes, `n = x^3 + y^3`
with `x, y ∈ ℚ` (data 1, 2, 6, 7, 8, 9, 12, 13, 15, …; offset 1).

The entry says: Alpöge, Bhargava and Shnidman prove "that the density of integers expressible as
the sum of two rational cubes is strictly positive and strictly less than 1" (lower density at
least 2/21, upper density at most 5/6), and "the authors remark that it is natural to conjecture
that these integers 'have natural density exactly 1/2.'"

`main` states this conjecture: `#{1 ≤ n ≤ N : n is a sum of two rational cubes} / N → 1/2`.
(The entry's other comment, a conjectured asymptotic from random matrix theory in Cohen (2007),
p. 378, is not spelled out in the entry and is not stated here.)
A small-height search (common denominator `d < 40`, numerators `|a|, |b| ≤ 120`) finds only
members of the listed data up to 45, as expected.
-/

namespace OMA.S_oeis_a159843

/-- `n` is a sum of two rational cubes. -/
def IsSumTwoRatCubes (n : ℕ) : Prop := ∃ x y : ℚ, x ^ 3 + y ^ 3 = n

/-- The number of `1 ≤ n ≤ N` that are sums of two rational cubes. -/
noncomputable def countUpTo (N : ℕ) : ℕ :=
  {n : ℕ | 1 ≤ n ∧ n ≤ N ∧ IsSumTwoRatCubes n}.ncard

open Filter Topology in
/-- Conjecture (Alpöge, Bhargava, Shnidman): the positive integers that are sums of two
rational cubes have natural density `1/2`. -/
theorem main : Tendsto (fun N : ℕ => (countUpTo N : ℝ) / N) atTop (𝓝 (1 / 2)) := by
  sorry

end OMA.S_oeis_a159843
