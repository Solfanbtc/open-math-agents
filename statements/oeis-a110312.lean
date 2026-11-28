import Mathlib

/-!
# A110312: Minimum number of polygonal pieces in a dissection of a regular n-gon into a square (conjectured).

Source: https://oeis.org/A110312
Credit: @Solfanbtc

The entry lists conjectured values `a(3), ..., a(20) = 4, 1, 6, 5, 7, 5, 9, 7, 10, 6, 11, 9, 11,
10, 12, 10, 13, 11` and hopes that "someone will establish the truth of some of the conjectured
values" (`a(4) = 1` is trivial, `a(3) = 4` is proved by Demaine, Kamata and Uehara, 2025).
`main` states that every listed value is the true minimum.

Conventions, following the entry:
* "Turning over is allowed": pieces are moved by arbitrary isometries of the plane
  (`EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)`, reflections included).
* Pieces are polygonal and "bounded by simple curves": each piece is a closed region bounded by a
  simple closed polygon (vertices `v 0, ..., v (m-1)`, `m ≥ 3`, edges `[v i, v (i+1 mod m)]`;
  consecutive edges meet only in their common vertex, non-consecutive edges are disjoint). The
  region is the boundary together with the points off the boundary whose connected component in
  the complement of the boundary is bounded (the inside, by the Jordan curve theorem).
* A dissection of `P` into `Q` with `k` pieces: `k` such pieces with union `P` and pairwise
  disjoint interiors, and isometries moving them to sets with union `Q` and pairwise disjoint
  interiors.
* The regular `n`-gon is the convex hull of `(cos (2πj/n), sin (2πj/n))`, `j < n`; its area is
  `(n/2) sin (2π/n)`, and the square is `[0, s]²` with `s² = (n/2) sin (2π/n)` (same area; the
  position and size of the polygons do not matter, as the problem is invariant under similarity).
* `a(n)` is the least `k` for which such a dissection exists.
-/

namespace OMA.S_oeis_a110312

open Real

/-- The plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- The edges of the closed polygon with vertices `v 0, ..., v (m-1)` are pairwise disjoint,
except that consecutive edges meet exactly in their common vertex. -/
def IsSimplePolygon {m : ℕ} (v : Fin m → Pt) : Prop :=
  ∀ i j : Fin m, i ≠ j →
    segment ℝ (v i) (v (finRotate m i)) ∩ segment ℝ (v j) (v (finRotate m j)) =
      if j = finRotate m i then {v j} else if i = finRotate m j then {v i} else ∅

/-- The boundary of the polygon with vertices `v`. -/
def polygonBoundary {m : ℕ} (v : Fin m → Pt) : Set Pt :=
  ⋃ i : Fin m, segment ℝ (v i) (v (finRotate m i))

/-- The closed region bounded by the polygon `v`: its boundary and the points of bounded
connected components of the complement of the boundary. -/
def polygonRegion {m : ℕ} (v : Fin m → Pt) : Set Pt :=
  polygonBoundary v ∪
    {x | x ∉ polygonBoundary v ∧
      Bornology.IsBounded (connectedComponentIn (polygonBoundary v)ᶜ x)}

/-- `S` is a closed region bounded by a simple closed polygon. -/
def IsPolygonalPiece (S : Set Pt) : Prop :=
  ∃ m : ℕ, 3 ≤ m ∧ ∃ v : Fin m → Pt, IsSimplePolygon v ∧ S = polygonRegion v

/-- `P` can be dissected into `k` polygonal pieces that can be rearranged (turning over allowed)
to form `Q`. -/
def IsDissection (P Q : Set Pt) (k : ℕ) : Prop :=
  ∃ (piece : Fin k → Set Pt) (g : Fin k → (Pt ≃ᵢ Pt)),
    (∀ i, IsPolygonalPiece (piece i)) ∧
    (⋃ i, piece i) = P ∧
    Pairwise (fun i j => Disjoint (interior (piece i)) (interior (piece j))) ∧
    (⋃ i, g i '' piece i) = Q ∧
    Pairwise (fun i j => Disjoint (interior (g i '' piece i)) (interior (g j '' piece j)))

/-- The regular `n`-gon inscribed in the unit circle. -/
noncomputable def regularPolygon (n : ℕ) : Set Pt :=
  convexHull ℝ (Set.range fun j : Fin n =>
    !₂[cos (2 * π * j / n), sin (2 * π * j / n)])

/-- The square `[0, s]²` with the same area `(n/2) sin (2π/n)` as `regularPolygon n`. -/
noncomputable def squareOfSameArea (n : ℕ) : Set Pt :=
  {x | ∀ i, 0 ≤ x i ∧ x i ≤ √((n / 2) * sin (2 * π / n))}

/-- A110312(n): the least number of pieces in a dissection of a regular `n`-gon into a square. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k | IsDissection (regularPolygon n) (squareOfSameArea n) k}

/-- The conjectured values `a(3), ..., a(20)` listed in A110312 are the true minima. -/
theorem main :
    ∀ n : ℕ, (hn : 3 ≤ n ∧ n ≤ 20) →
      a n = [4, 1, 6, 5, 7, 5, 9, 7, 10, 6, 11, 9, 11, 10, 12, 10, 13, 11].get
        ⟨n - 3, by simp; omega⟩ := by
  sorry

end OMA.S_oeis_a110312
