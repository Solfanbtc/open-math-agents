import Mathlib

/-!
# A238822: Number of equilateral triangles bounded by the sides and diagonals of a regular 3n-gon.

Source: https://oeis.org/A238822
Credit: @Solfanbtc

Conjecture (V. Lendvaj, Jul 24 2024, in the FORMULA section): for odd n,
a(n) = n*(n+1)^3/2 - 3*n^2.

Conventions.
* The regular 3n-gon has vertices `exp(2πik/(3n))`, `k < 3n`, in `ℂ` (the count is invariant
  under similarity). Its sides and diagonals are the closed segments between two distinct vertices.
* A triangle is "bounded by the sides and diagonals" when each of its three sides lies inside
  one of these segments (its vertices are then crossing points of the drawing). Since the polygon
  is strictly convex, two chords on a common line coincide, so "covered by the drawing" and
  "contained in a single chord" agree. Triangles of all sizes are counted, not only faces.
* A triangle is counted as its set of three vertices.
This reading reproduces the data: a(1..5) = 1, 14, 69, 188, 465 (checked numerically).
The conjectured formula matches at n = 1, 3, 5 (1, 69, 465). `n*(n+1)^3` is even for odd `n`,
and the division is taken in `ℚ`.
-/

namespace OMA.S_oeis_a238822

open Complex

/-- The `k`-th vertex of the regular `3n`-gon inscribed in the unit circle. -/
noncomputable def vertex (n k : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * I * k / (3 * n))

/-- `x` and `y` lie on a common side or diagonal of the regular `3n`-gon, i.e. the segment
`[x, y]` is contained in one of them. -/
def OnChord (n : ℕ) (x y : ℂ) : Prop :=
  ∃ i < 3 * n, ∃ j < 3 * n, i ≠ j ∧
    x ∈ segment ℝ (vertex n i) (vertex n j) ∧ y ∈ segment ℝ (vertex n i) (vertex n j)

/-- Vertex sets of the equilateral triangles bounded by the sides and diagonals of the
regular `3n`-gon. -/
def triangles (n : ℕ) : Set (Finset ℂ) :=
  {T | ∃ x y z : ℂ, T = {x, y, z} ∧ x ≠ y ∧ dist x y = dist y z ∧ dist y z = dist z x ∧
    OnChord n x y ∧ OnChord n y z ∧ OnChord n z x}

/-- A238822: the number of such triangles. -/
noncomputable def a (n : ℕ) : ℕ := (triangles n).ncard

theorem main : ∀ n : ℕ, Odd n →
    (a n : ℚ) = (n : ℚ) * ((n : ℚ) + 1) ^ 3 / 2 - 3 * (n : ℚ) ^ 2 := by
  sorry

end OMA.S_oeis_a238822
