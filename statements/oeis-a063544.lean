import Mathlib

/-!
# A063544: Smallest number of triangulations of n points in the plane.

Source: https://oeis.org/A063544
Credit: @Solfanbtc

Conjecture (M. Scheucher, Aug 22 2016, in the FORMULA section): a(n) = sqrt(12)^(n - Θ(log n)).

Stated as: there is `f : ℕ → ℝ` with a(n) = sqrt(12)^(n - f(n)) for all n ≥ 3 (the offset) and
`f = Θ(log n)` as n → ∞ (Mathlib's `Asymptotics.IsTheta` along `atTop`). Since a(n) ≥ 1, such an
`f` is unique on n ≥ 3, so this is exactly the source's claim.

The same entry's COMMENT contains a second, separate conjecture (that "double circles" minimize
the number of triangulations). It is not included: the entry describes the double circle only
informally ("half of the points are extremal", interior points "arbitrarily close" to the hull
edges), without fixing it for odd n, so it cannot be stated faithfully from the source.

Conventions (as in Aichholzer–Hurtado–Noy and the other linked papers):
* "n points in the plane" means a set of n points in general position (no three collinear).
  Without this the minimum would degenerate (e.g. points on a line have no triangulation).
* A triangulation of a point set `P` in general position is a maximal set of pairwise
  non-crossing segments with endpoints in `P`. Two distinct segments cross iff their relative
  interiors meet. In general position, segments that share an endpoint never cross, and no
  segment passes through a third point of `P`.
* a(n) is the minimum, over all such `P` with `n` points, of the number of triangulations.
  Values: a(3..15) = 1, 1, 2, 4, 11, 30, 89, 250, 776, 2236, 7147, 20979, 68448.
-/

namespace OMA.S_oeis_a063544

open Asymptotics Filter

/-- Points of the Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- No three points of `P` are collinear. -/
def InGeneralPosition (P : Finset Pt) : Prop :=
  ∀ s ⊆ P, s.card = 3 → ¬ Collinear ℝ (s : Set Pt)

/-- The relative interior of the segment with the given (unordered) endpoints. -/
def openSeg (e : Sym2 Pt) : Set Pt :=
  Sym2.lift ⟨fun p q => openSegment ℝ p q, fun p q => openSegment_symm ℝ p q⟩ e

/-- The segments with two distinct endpoints in `P`. -/
def edges (P : Finset Pt) : Set (Sym2 Pt) := {e | e ∈ P.sym2 ∧ ¬ e.IsDiag}

/-- A set of segments is non-crossing if distinct segments have disjoint relative interiors. -/
def IsNonCrossing (T : Set (Sym2 Pt)) : Prop :=
  ∀ e ∈ T, ∀ e' ∈ T, e ≠ e' → Disjoint (openSeg e) (openSeg e')

/-- A triangulation of `P`: a maximal non-crossing set of segments between points of `P`. -/
def IsTriangulation (P : Finset Pt) (T : Set (Sym2 Pt)) : Prop :=
  T ⊆ edges P ∧ IsNonCrossing T ∧
    ∀ T' : Set (Sym2 Pt), T ⊆ T' → T' ⊆ edges P → IsNonCrossing T' → T' = T

/-- The number of triangulations of `P`. -/
noncomputable def numTriangulations (P : Finset Pt) : ℕ :=
  {T : Set (Sym2 Pt) | IsTriangulation P T}.ncard

/-- A063544: the smallest number of triangulations of `n` points in general position. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ P : Finset Pt, P.card = n ∧ InGeneralPosition P ∧ numTriangulations P = k}

theorem main : ∃ f : ℕ → ℝ,
    (∀ n : ℕ, 3 ≤ n → (a n : ℝ) = Real.sqrt 12 ^ ((n : ℝ) - f n)) ∧
    f =Θ[atTop] (fun n : ℕ => Real.log n) := by
  sorry

end OMA.S_oeis_a063544
