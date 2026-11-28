import Mathlib

/-!
# A084826: Best packing of m>1 equal spheres in a cube setting a new density record.

Source: https://oeis.org/A084826
Credit: @Solfanbtc

Data: 2, 3, 4, 6, 7, 8, 31, 32, 48, 60, 61, 62, 63.
The comment says that the terms ≥ 31 are only conjectures found by numerical experimentation
(Pfoertner's table). The claim stated here is that the listed terms are exactly the record
values of `m` in the range 2 ≤ m ≤ 63, i.e. that the sequence begins with the 13 listed terms.

Conventions.
* The container is the unit cube [0,1]^3 (density does not depend on the side length).
* `m` equal closed balls of radius `r` with centres `c i` fit in the cube without overlapping
  iff every coordinate of every centre lies in [r, 1 - r] and distinct centres are at
  Euclidean distance ≥ 2r (interiors disjoint; touching allowed).
* `maxRadius m` is the supremum of the feasible radii (it is attained, by compactness), and the
  best packing density of `m` spheres is `m * (4/3) * π * maxRadius m ^ 3` (cube volume 1).
* `m` sets a new density record when m ≥ 2 (the sequence starts at m > 1) and its best density
  is strictly larger than the best density of every k with 2 ≤ k < m.
-/

namespace OMA.S_oeis_a084826

open Real

/-- `m` balls of radius `r` can be packed in the unit cube `[0,1]^3`. -/
def Feasible (m : ℕ) (r : ℝ) : Prop :=
  ∃ c : Fin m → EuclideanSpace ℝ (Fin 3),
    (∀ i, ∀ j : Fin 3, r ≤ c i j ∧ c i j ≤ 1 - r) ∧
    (∀ i i', i ≠ i' → 2 * r ≤ dist (c i) (c i'))

/-- The radius of the best packing of `m` equal spheres in the unit cube. -/
noncomputable def maxRadius (m : ℕ) : ℝ := sSup {r : ℝ | 0 ≤ r ∧ Feasible m r}

/-- The density of the best packing of `m` equal spheres in the unit cube. -/
noncomputable def density (m : ℕ) : ℝ := m * (4 / 3) * π * maxRadius m ^ 3

/-- `m > 1` sets a new density record. -/
def IsRecord (m : ℕ) : Prop :=
  2 ≤ m ∧ ∀ k : ℕ, 2 ≤ k → k < m → density k < density m

theorem main : ∀ m : ℕ, m ≤ 63 →
    (IsRecord m ↔ m ∈ ({2, 3, 4, 6, 7, 8, 31, 32, 48, 60, 61, 62, 63} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a084826
