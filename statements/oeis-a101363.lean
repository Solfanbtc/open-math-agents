import Mathlib

/-!
# A101363: In the interior of a regular 2n-gon with all diagonals drawn, the number of points where exactly three diagonals intersect.

Source: https://oeis.org/A101363
Credit: @Solfanbtc

Conjecture (G. McRae, in the comments of A101363, checked up to n = 210): an n-gon with
n = 30k has 5n points where 6 or 7 diagonals meet and no points where more than 7 diagonals
meet; if k is odd, then 6 diagonals meet in each of 4n points and 7 diagonals meet in each
of n points; if k is even, then no groups of exactly 6 diagonals meet in a point, while
exactly 7 diagonals meet in each of 5n points.

Conventions.
* The regular n-gon has vertices `exp(2πik/n)`, `k : Fin n`, in `ℂ` (viewed as a real plane);
  its interior is the topological interior of their convex hull.
* A diagonal is a segment between two non-adjacent vertices (sides are not diagonals);
  `diagonalsThrough n P` is the number of diagonals (as closed segments) containing `P`.
  For an interior point `P` this is the number of diagonals meeting at `P`.
* Minimal fix: for n = 30k all n/2 = 15k diameters pass through the center, so the clause
  "no points where more than 7 diagonals meet" is literally false at the center. That clause
  is stated for interior points other than the center (as in Poonen–Rubinstein, where the
  center is treated separately). The center never has 6 or 7 diagonals (15k ≥ 15), so the
  counting clauses are unaffected and are stated over all interior points.
* Checked numerically (floating-point clustering): the 30-gon has 120 points with exactly 6
  diagonals and 30 with exactly 7, and no non-center point with more than 7; the 60-gon has
  none with 6 and 300 with 7; the 12-gon has 60 points with exactly 3 (= A101363(6)).
-/

namespace OMA.S_oeis_a101363

open Complex

/-- The `k`-th vertex of the regular `n`-gon inscribed in the unit circle. -/
noncomputable def vertex (n : ℕ) (k : Fin n) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (k.val : ℂ) / (n : ℂ))

/-- `d = (i, j)` with `i < j` is a diagonal: the vertices `i, j` are not adjacent. -/
def IsDiagonal (n : ℕ) (d : Fin n × Fin n) : Prop :=
  d.1 < d.2 ∧ d.2.val - d.1.val ≠ 1 ∧ ¬ (d.1.val = 0 ∧ d.2.val = n - 1)

/-- The interior of the regular `n`-gon. -/
noncomputable def polygonInterior (n : ℕ) : Set ℂ :=
  interior (convexHull ℝ (Set.range (vertex n)))

/-- The number of diagonals of the regular `n`-gon passing through `P`. -/
noncomputable def diagonalsThrough (n : ℕ) (P : ℂ) : ℕ :=
  Set.ncard {d : Fin n × Fin n | IsDiagonal n d ∧ P ∈ segment ℝ (vertex n d.1) (vertex n d.2)}

/-- The number of interior points of the regular `n`-gon where exactly `m` diagonals meet. -/
noncomputable def pointsWith (n m : ℕ) : ℕ :=
  Set.ncard {P : ℂ | P ∈ polygonInterior n ∧ diagonalsThrough n P = m}

theorem main : ∀ k : ℕ, 1 ≤ k →
    (∀ P ∈ polygonInterior (30 * k), P ≠ 0 → diagonalsThrough (30 * k) P ≤ 7) ∧
    Set.ncard {P : ℂ | P ∈ polygonInterior (30 * k) ∧
      (diagonalsThrough (30 * k) P = 6 ∨ diagonalsThrough (30 * k) P = 7)} = 5 * (30 * k) ∧
    (Odd k → pointsWith (30 * k) 6 = 4 * (30 * k) ∧ pointsWith (30 * k) 7 = 30 * k) ∧
    (Even k → pointsWith (30 * k) 6 = 0 ∧ pointsWith (30 * k) 7 = 5 * (30 * k)) := by
  sorry

end OMA.S_oeis_a101363
