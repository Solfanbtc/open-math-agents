import Mathlib

/-!
# A080865: Order of symmetry groups of n points on 3-dimensional sphere with minimal distance between them maximized, also known as hostile neighbor or Tammes problem.

Source: https://oeis.org/A080865
Credit: @Solfanbtc

The sequence (offset 4) is `24, 12, 48, 6, 16, 12, 4, 10, 120, 8, 8` for `n = 4, ..., 14`.
OEIS comment: if more than one best packing exists for a given `n`, the one with the largest
symmetry group is chosen. Conjecture (OEIS comment): the sequence continues, for
`n = 15, ..., 50`, with
`3, 16, 4, 2, 2, 12, 1, 1, 1, 24, 3, 2, 4, 1, 1, 6, 5, 6, 3, 2, 1, 4, 2, 24, 1, 3, 1, 10, 1, 2,
1, 2, 1, 24, 2, 12` (the value at `n = 24`, the snub cube, is a theorem of Robinson; the others
are conjectural; `main` states all 36 values).

Conventions.
* A configuration is a finite set `X` of `n` points of the unit sphere `S²` of `ℝ³`
  (`EuclideanSpace ℝ (Fin 3)`).
* `X` is a best packing (Tammes-optimal) if its minimal pairwise distance is maximal among all
  `n`-point configurations; this is phrased without `inf`: every separation `r` achieved by some
  `n`-point configuration `Y` (all distinct pairs of `Y` at distance `≥ r`) is achieved by `X`.
* The symmetry group of `X` is the group of linear isometries of `ℝ³` (the full orthogonal group
  `O(3)`, reflections included) mapping `X` onto `X`; this matches the data: `24` (tetrahedron,
  `T_d`), `48` (octahedron, `O_h`), `120` (icosahedron, `I_h`), and `24` for the chiral snub cube.
* `a(n)` is the largest symmetry order among best packings, so the claim `a(n) = v` is
  `IsGreatest (symOrders n) v`.
-/

namespace OMA.S_oeis_a080865

/-- Three-dimensional Euclidean space. -/
abbrev E := EuclideanSpace ℝ (Fin 3)

/-- `X` is an `n`-point configuration on the unit sphere. -/
def IsConfig (n : ℕ) (X : Finset E) : Prop :=
  X.card = n ∧ ∀ x ∈ X, ‖x‖ = 1

/-- All distinct points of `X` are at distance at least `r`. -/
def Separated (r : ℝ) (X : Finset E) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y → r ≤ dist x y

/-- `X` is a best packing of `n` points: its minimal distance is maximal. -/
def IsBestPacking (n : ℕ) (X : Finset E) : Prop :=
  IsConfig n X ∧ ∀ Y : Finset E, IsConfig n Y → ∀ r : ℝ, Separated r Y → Separated r X

/-- Order of the symmetry group of `X`: linear isometries of `ℝ³` mapping `X` onto itself. -/
noncomputable def symOrder (X : Finset E) : ℕ :=
  Nat.card {g : E ≃ₗᵢ[ℝ] E // g '' (X : Set E) = X}

/-- Symmetry orders of the best packings of `n` points. -/
def symOrders (n : ℕ) : Set ℕ :=
  {k | ∃ X : Finset E, IsBestPacking n X ∧ symOrder X = k}

/-- Conjectured values of A080865 for `n = 15, ..., 50` (index `i` is `n = i + 15`). -/
def conjValues : Fin 36 → ℕ :=
  ![3, 16, 4, 2, 2, 12, 1, 1, 1, 24, 3, 2, 4, 1, 1, 6, 5, 6, 3, 2, 1, 4, 2, 24, 1, 3, 1, 10,
    1, 2, 1, 2, 1, 24, 2, 12]

/-- The conjectured continuation of A080865: for `15 ≤ n ≤ 50`, the largest symmetry group
order of a best packing of `n` points on `S²` is the listed value. -/
theorem main : ∀ i : Fin 36, IsGreatest (symOrders (i.val + 15)) (conjValues i) := by
  sorry

end OMA.S_oeis_a080865
