import Mathlib

/-!
# A036496: Number of lines that intersect the first n points on a spiral on a triangular lattice.

Source: https://oeis.org/A036496
Credit: @Solfanbtc

Conjecture (Winston C. Yang, Apr 06 2002, in the entry): a(n) is half the minimal perimeter of a
polyhex of n hexagons. The entry adds (Sascha Kurz, Mar 17 2008): "This conjecture follows from
the Brunvoll et al. reference" (J. Brunvoll, B. N. Cyvin, S. J. Cyvin, More about extremal
animals, J. Math. Chem. 12 (1993), 109-119; see also Harary–Harborth, Extremal animals, 1976,
for the minimal perimeter 2⌈√(12n-3)⌉). So the conjecture is reported as proved.

Conventions.
* Points of the triangular lattice are written in axial coordinates: `(a, b)` is the point
  `a·(1, 0) + b·(1/2, √3/2)`. The lattice lines are the horizontal lines (`b` constant), the
  lines at 60 degrees (`a` constant) and the lines at 120 degrees (`a + b` constant), so a(n)
  is the number of distinct values of `b`, of `a` and of `a + b` among the first n points.
* The spiral starts at (0,0), (1,0), (1/2, √3/2) = (0,1) and continues counterclockwise,
  hugging the previous turns: ring `k ≥ 1` starts at `(k, 1-k)` (one step right of the end
  `(k-1, 1-k)` of ring `k-1`), goes up to `(k, 0)`, then along the sides of the hexagon of
  radius `k` through `(0, k)`, `(-k, k)`, `(-k, 0)`, `(0, -k)`, and ends at `(k, -k)`; it has
  `6k` points. Checked in python3: consecutive points are adjacent, all points are distinct,
  and the resulting a(n) agrees with all 72 listed terms of %S/%T/%U and with
  a(n) = ⌈√(12n-3)⌉ for 1 ≤ n ≤ 1000.
* A polyhex of n hexagons is a set of n cells of the hexagonal tiling, connected through shared
  edges. The cells are the points of the triangular lattice (each hexagon's centre), two cells
  sharing an edge iff they differ by one of the six unit vectors. Its perimeter is the number
  of hexagon edges between a cell of the polyhex and a cell outside it (`6n - 2·#shared edges`);
  edges around holes are counted, which does not change the minimum (a polyhex with a hole
  never has minimal perimeter, and in any case minimal perimeter equals
  `6n - 2·(max number of shared edges)`). Checked by brute force for n ≤ 9: the minimal
  perimeter is 2·a(n).
* n = 0 is excluded: there is no polyhex of 0 hexagons (a(0) = 0 is a convention of the line
  count), so the claim is for n ≥ 1.
-/

namespace OMA.S_oeis_a036496

/-- Ring `k` of the hexagonal spiral, in order (6k points for k ≥ 1). -/
def ring (k : ℕ) : List (ℤ × ℤ) :=
  let K : ℤ := k
  [(K, 1 - K)] ++ (List.range (k - 1)).map (fun j => (K, 2 - K + j)) ++
    (List.range k).map (fun j => (K - 1 - j, 1 + (j : ℤ))) ++
    (List.range k).map (fun j => (-1 - (j : ℤ), K)) ++
    (List.range k).map (fun j => (-K, K - 1 - j)) ++
    (List.range k).map (fun j => (1 - K + j, -1 - (j : ℤ))) ++
    (List.range k).map (fun j => (1 + (j : ℤ), -K))

/-- The spiral up to the end of ring `r`: (0,0), then rings 1, ..., r. -/
def spiralUpTo (r : ℕ) : List (ℤ × ℤ) :=
  (0, 0) :: (List.range r).flatMap (fun k => ring (k + 1))

/-- The first `n` points of the spiral (ring `n` is never needed, as rings have ≥ 1 point). -/
def firstPoints (n : ℕ) : List (ℤ × ℤ) := (spiralUpTo n).take n

/-- A036496: the number of lattice lines (three directions) meeting the first `n` points. -/
def a (n : ℕ) : ℕ :=
  ((firstPoints n).map Prod.snd).toFinset.card +
    ((firstPoints n).map Prod.fst).toFinset.card +
    ((firstPoints n).map fun p => p.1 + p.2).toFinset.card

/-- The six unit vectors of the triangular lattice in axial coordinates. -/
def dirs : Finset (ℤ × ℤ) := {(1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1)}

/-- Two hexagons share an edge iff their centres differ by a unit vector. -/
def hexAdj : SimpleGraph (ℤ × ℤ) := SimpleGraph.fromRel fun p q => q - p ∈ dirs

/-- Perimeter of a set of hexagons: edges between a cell of `S` and a cell outside `S`. -/
def perimeter (S : Finset (ℤ × ℤ)) : ℕ :=
  ∑ c ∈ S, (dirs.filter fun d => c + d ∉ S).card

/-- `S` is a polyhex: a set of hexagons connected through shared edges. -/
def IsPolyhex (S : Finset (ℤ × ℤ)) : Prop :=
  (hexAdj.induce (S : Set (ℤ × ℤ))).Connected

theorem main : ∀ n : ℕ, 1 ≤ n →
    IsLeast {p : ℕ | ∃ S : Finset (ℤ × ℤ), S.card = n ∧ IsPolyhex S ∧ perimeter S = p}
      (2 * a n) := by
  sorry

end OMA.S_oeis_a036496
