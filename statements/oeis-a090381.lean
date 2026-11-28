import Mathlib

/-!
# A090381: Expansion of (1+4x+7x^2)/((1-x)^2*(1-x^2)).

Source: https://oeis.org/A090381
Credit: @Solfanbtc

Conjecture (Nicolas Nagel, Sep 09 2016, in the %C lines): `a(n)` is the maximum number of areas
that are defined by the `3n` angle `(n+1)`-sectors in a triangle.

Formalization:
* `a(n)`: the entry gives `a(n) = 3n(n+1) + (1 + (-1)^n)/2` (Wesley Ivan Hurt), equivalent to the
  defining g.f.; we write it as `3n(n+1) + [n even]`. It reproduces the listed terms
  `1, 6, 19, 36, 61, 90, …` (offset 0).
* A triangle is three affinely independent points `A, B, C` of the Euclidean plane.
* The angle `(n+1)`-sectors at the vertex `A` are the `n` segments from `A` to the points `Q` of
  the opposite side `[B, C]` with `∠BAQ = j/(n+1) · ∠BAC`, `j = 1, …, n`; they cut the angle at `A`
  into `n + 1` equal angles (measuring from the side `AC` instead gives the same `n` segments,
  `j ↦ n + 1 - j`). Likewise at `B` (from side `BC`, points of `[C, A]`) and `C` (from side `CA`,
  points of `[A, B]`): `3n` segments in all.
* The areas defined by them are the connected components of the open triangle (interior of the
  convex hull of `A, B, C`) with the `3n` segments removed; their number is the `Nat.card` of the
  type of connected components.
* "Maximum" is over all triangles: `a(n)` is the greatest such number (`IsGreatest`), for every
  `n ≥ 0`. (For `n = 0` there are no sectors and one area; for `n = 1` the three bisectors meet at
  the incenter, giving `6` areas.)
-/

open EuclideanGeometry

namespace OMA.S_oeis_a090381

/-- The plane. -/
abbrev P := EuclideanSpace ℝ (Fin 2)

/-- A090381: `a(n) = 3n(n+1) + (1 + (-1)^n)/2`. -/
def a (n : ℕ) : ℕ := 3 * n * (n + 1) + if Even n then 1 else 0

/-- The union of the `n` angle `(n+1)`-sectors at the vertex `A` of the triangle `ABC`: the segments
from `A` to the points `Q ∈ [B, C]` with `∠BAQ = j/(n+1) · ∠BAC`, `1 ≤ j ≤ n`. -/
def sectorsAt (n : ℕ) (A B C : P) : Set P :=
  ⋃ j ∈ Finset.Icc 1 n,
    {X | ∃ Q ∈ segment ℝ B C, ∠ B A Q = (j : ℝ) / (n + 1) * ∠ B A C ∧ X ∈ segment ℝ A Q}

/-- The `3n` angle `(n+1)`-sectors of the triangle `ABC`. -/
def sectors (n : ℕ) (A B C : P) : Set P :=
  sectorsAt n A B C ∪ sectorsAt n B C A ∪ sectorsAt n C A B

/-- The number of areas into which the `3n` angle `(n+1)`-sectors cut the triangle `ABC`. -/
noncomputable def areas (n : ℕ) (A B C : P) : ℕ :=
  Nat.card (ConnectedComponents ↥(interior (convexHull ℝ {A, B, C}) \ sectors n A B C))

/-- Nagel's conjecture: the maximum, over all triangles, of the number of areas defined by the
`3n` angle `(n+1)`-sectors is `a(n)`. -/
theorem main : ∀ n : ℕ,
    IsGreatest {k | ∃ A B C : P, AffineIndependent ℝ ![A, B, C] ∧ areas n A B C = k} (a n) := by
  sorry

end OMA.S_oeis_a090381
