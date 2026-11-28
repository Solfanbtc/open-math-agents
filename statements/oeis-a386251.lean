import Mathlib

/-!
# A386251: Shortest closed walk via noncongruent full-dimensional integer-length lattice diagonals

Source: https://oeis.org/A386251
Credit: @Solfanbtc

Consider the graph whose vertices are the points of the n-dimensional cubic lattice `ℤ^n`, with
points connected by all integer-length diagonals that traverse all n dimensions and do not
intersect intermediate points. a(n) is the total length of the shortest possible closed walk in
this graph via noncongruent diagonals.

Conjecture (in the entry, Charles L. Hohn, 2025): for all n ≥ 6, a(n) is produced by 3-segment
walks, i.e. some closed walk with exactly 3 segments attains the minimum total length.

Conventions.
* A diagonal (edge direction) is a vector `v ∈ ℤ^n` with every coordinate nonzero ("traverses all
  n dimensions"), with coprime coordinates ("does not intersect intermediate lattice points"),
  and whose Euclidean length is an integer (`∑ vᵢ²` is a perfect square). Its length is
  `√(∑ vᵢ²)`.
* By translation invariance, a closed walk with k segments is a k-tuple of diagonals summing to
  0; we require k ≥ 1 (the empty walk is not a walk "via diagonals").
* "Noncongruent": the entry's example a(3) = 28 uses two segments of the same length 9,
  `[-7,4,4]` and `[8,-4,1]`, so congruence is congruence under the symmetries of the lattice
  (coordinate permutations and sign changes): two diagonals are congruent iff their multisets of
  absolute coordinate values agree. Segments are required pairwise noncongruent.
* "a(n) is produced by 3-segment walks" is read as: some 3-segment closed walk has total length
  ≤ that of every closed walk. (Sanity check by search: for n = 6 the best 3-segment walk has
  length 18 = a(6), e.g. (1,1,1,1,4,4) + (2,1,2,1,-1,-5) + (-3,-2,-3,-2,-3,1) = 0; no 3-segment
  walk with segment lengths ≤ 12 exists for n = 3, 4, 5, consistent with the entry.)
-/

namespace OMA.S_oeis_a386251

/-- An edge direction of the graph: all coordinates nonzero, coprime, integer length. -/
def IsDiagonal {n : ℕ} (v : Fin n → ℤ) : Prop :=
  (∀ i, v i ≠ 0) ∧ Finset.univ.gcd v = 1 ∧ IsSquare (∑ i, (v i) ^ 2)

/-- Euclidean length of an integer-length diagonal. -/
def len {n : ℕ} (v : Fin n → ℤ) : ℕ := Nat.sqrt (∑ i, (v i).natAbs ^ 2)

/-- Congruence under the lattice symmetries (signed permutations of coordinates). -/
def Congruent {n : ℕ} (v w : Fin n → ℤ) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), ∀ i, |v (σ i)| = |w i|

/-- A closed walk with `k ≥ 1` segments via pairwise noncongruent diagonals. -/
def IsClosedWalk {n k : ℕ} (w : Fin k → Fin n → ℤ) : Prop :=
  0 < k ∧ (∀ j, IsDiagonal (w j)) ∧ (∀ j j', j ≠ j' → ¬ Congruent (w j) (w j')) ∧
    ∑ j, w j = 0

/-- Total length of a walk. -/
def totalLength {n k : ℕ} (w : Fin k → Fin n → ℤ) : ℕ := ∑ j, len (w j)

theorem main : ∀ n : ℕ, 6 ≤ n →
    ∃ w : Fin 3 → Fin n → ℤ, IsClosedWalk w ∧
      ∀ (k : ℕ) (w' : Fin k → Fin n → ℤ), IsClosedWalk w' → totalLength w ≤ totalLength w' := by
  sorry

end OMA.S_oeis_a386251
