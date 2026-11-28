import Mathlib

/-!
# Kusner's conjecture

Source: https://en.wikipedia.org/wiki/Kusner_conjecture (redirects to "Equilateral dimension")
Credit: @Solfanbtc

From the source: the equilateral dimension of a metric space is the maximum size of any subset
of the space whose points are all at equal distances to each other. The equilateral dimension of
`d`-dimensional Euclidean space is `d + 1`, and that of a `d`-dimensional vector space with the
Chebyshev (`L^∞`) distance is `2 ^ d`; but the equilateral dimension of a space with the
Manhattan distance (`L^1` norm) is not known. Kusner's conjecture, named after Robert B. Kusner,
states that it is exactly `2 d`, achieved by the vertices of a cross polytope.

Encoding: the space is `Fin d → ℝ` with the Manhattan distance `∑ i, |x i - y i|`, and "the
equilateral dimension is exactly `2 d`" says that `2 d` is the greatest size of a finite set of
pairwise equidistant points. The case `d = 0` is excluded: that space is a single point, whose
equilateral dimension is `1`, so the formula `2 d` is meant for `d ≥ 1`.
-/

namespace OMA.S_wp_kusner_conjecture

/-- The Manhattan (`L^1`) distance on `Fin d → ℝ`. -/
def manhattanDist {d : ℕ} (x y : Fin d → ℝ) : ℝ := ∑ i, |x i - y i|

/-- `S` is equilateral for the Manhattan distance: all its points are at the same distance from
each other. -/
def IsEquilateral {d : ℕ} (S : Finset (Fin d → ℝ)) : Prop :=
  ∃ r : ℝ, ∀ x ∈ S, ∀ y ∈ S, x ≠ y → manhattanDist x y = r

/-- **Kusner's conjecture**: for every `d ≥ 1`, the largest size of a set of pairwise
equidistant points of `ℝ ^ d` for the Manhattan distance is `2 d`. -/
theorem main : ∀ d : ℕ, 1 ≤ d →
    IsGreatest {k : ℕ | ∃ S : Finset (Fin d → ℝ), S.card = k ∧ IsEquilateral S} (2 * d) := by
  sorry

end OMA.S_wp_kusner_conjecture
