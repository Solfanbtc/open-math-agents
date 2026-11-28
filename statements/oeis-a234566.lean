import Mathlib

/-!
# A234566: 1/a(n) is the area of the smallest triangle delimited by 3 lines each passing through at least 2 points of an n X n unitary spaced grid.

Source: https://oeis.org/A234566
Credit: @Solfanbtc

The grid is `{0, ..., n-1}²`. Consider the lines passing through at least 2 grid points, and the
non-degenerate triangles delimited by 3 such lines (pairwise non-parallel, not concurrent). Let
`A(n)` be the smallest area of such a triangle; the entry defines `a(n) = 1 / A(n)`
(`4, 30, 770, 5148, ...` for `n = 2, 3, 4, 5`).

Conjecture (the entry): the sequence is well-defined, i.e. `a(n)` is an integer for every
`n > 1`. Stated as: for every `n ≥ 2` the set of areas has a least element, of the form `1 / m`
for a positive integer `m`.

Conventions:
* A line is given by two distinct grid points `P ≠ Q`; its equation is `a x + b y = c` with
  `a = Q.2 - P.2`, `b = P.1 - Q.1`, `c = a P.1 + b P.2`. Two lines are non-parallel iff
  `a₁ b₂ - a₂ b₁ ≠ 0`, and then they meet at the point given by Cramer's rule (`meet`).
* The triangle's vertices are the three pairwise intersection points, its area is given by the
  shoelace formula; non-degenerate means pairwise non-parallel lines and positive area (three
  concurrent lines give area `0`).
* A python3 computation with exactly these formulas gives minimal areas `1/4, 1/30, 1/770,
  1/5148` for `n = 2, 3, 4, 5`, matching the data.
-/

namespace OMA.S_oeis_a234566

/-- The `n × n` grid `{0, ..., n-1}²`. -/
def grid (n : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.range n).image (fun i : ℕ => (i : ℤ))) ×ˢ ((Finset.range n).image (fun i : ℕ => (i : ℤ)))

/-- Coefficients `(a, b, c)` of the line `a x + b y = c` through `P` and `Q`. -/
def lineThrough (P Q : ℤ × ℤ) : ℚ × ℚ × ℚ :=
  let a : ℚ := Q.2 - P.2
  let b : ℚ := P.1 - Q.1
  (a, b, a * P.1 + b * P.2)

/-- `a₁ b₂ - a₂ b₁`: nonzero iff the two lines are not parallel. -/
def cross (l₁ l₂ : ℚ × ℚ × ℚ) : ℚ := l₁.1 * l₂.2.1 - l₂.1 * l₁.2.1

/-- The intersection point of two non-parallel lines (Cramer's rule). -/
def meet (l₁ l₂ : ℚ × ℚ × ℚ) : ℚ × ℚ :=
  ((l₁.2.2 * l₂.2.1 - l₂.2.2 * l₁.2.1) / cross l₁ l₂,
    (l₁.1 * l₂.2.2 - l₂.1 * l₁.2.2) / cross l₁ l₂)

/-- Area of the triangle `u v w` (shoelace formula). -/
def area (u v w : ℚ × ℚ) : ℚ :=
  |(v.1 - u.1) * (w.2 - u.2) - (w.1 - u.1) * (v.2 - u.2)| / 2

/-- Areas of the non-degenerate triangles delimited by 3 lines, each through 2 distinct grid
points. -/
def areas (n : ℕ) : Set ℚ :=
  {A | ∃ P₁ ∈ grid n, ∃ Q₁ ∈ grid n, ∃ P₂ ∈ grid n, ∃ Q₂ ∈ grid n, ∃ P₃ ∈ grid n, ∃ Q₃ ∈ grid n,
    P₁ ≠ Q₁ ∧ P₂ ≠ Q₂ ∧ P₃ ≠ Q₃ ∧
    cross (lineThrough P₁ Q₁) (lineThrough P₂ Q₂) ≠ 0 ∧
    cross (lineThrough P₁ Q₁) (lineThrough P₃ Q₃) ≠ 0 ∧
    cross (lineThrough P₂ Q₂) (lineThrough P₃ Q₃) ≠ 0 ∧
    0 < A ∧
    A = area (meet (lineThrough P₁ Q₁) (lineThrough P₂ Q₂))
      (meet (lineThrough P₁ Q₁) (lineThrough P₃ Q₃))
      (meet (lineThrough P₂ Q₂) (lineThrough P₃ Q₃))}

/-- Conjecture: for every `n > 1`, the smallest triangle area is `1 / a(n)` with `a(n)` a positive
integer. -/
theorem main : ∀ n : ℕ, 2 ≤ n → ∃ m : ℕ, 0 < m ∧ IsLeast (areas n) (1 / (m : ℚ)) := by
  sorry

end OMA.S_oeis_a234566
