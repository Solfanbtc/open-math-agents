import Mathlib

/-!
# A084829: Best packing of m>1 equal spheres in a sphere setting a new density record.

Source: https://oeis.org/A084829
Credit: @Solfanbtc

The entry lists 2, 3, 4, 6, 8, 9, 11, 12, 18, 21, 25, 30, 31, 32, 33, 34, 35, 36, 38, 49, 51,
53, 56, 59, 60, 61 and says: "All terms beyond m=9 are only conjectures found by numerical
experimentation." The claim of the entry is that these are exactly the record-setting values
of m in the range 1 < m ≤ 61 (the terms are consecutive terms of the sequence, so no record
is missing in between). It is stated here for the whole list; the part m ≤ 9 is claimed as known.

Conventions (from the entry's comment and the linked tables):
* `r m` is the largest radius of `m` equal balls with pairwise disjoint interiors inside the
  unit ball of ℝ³: centers `c i` with `‖c i‖ + r ≤ 1` and `2 r ≤ dist (c i) (c j)` for `i ≠ j`.
* The density of the best packing is `m * r(m)^3` (fraction of the volume of the big ball
  occupied by the small ones). For m = 2 it is 2 * (1/2)^3 = 0.25, as the entry says.
* m > 1 sets a new density record when its density exceeds that of every j with 1 < j < m
  (m = 1, density 1, is excluded by the title).
The comment's remark that 31 is the first known configuration of density above 0.5 is a report
of numerical findings, not a separate claim, and is not stated.
-/

namespace OMA.S_oeis_a084829

/-- Points of Euclidean 3-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The largest radius of `m` equal non-overlapping balls inside the unit ball of ℝ³. -/
noncomputable def r (m : ℕ) : ℝ :=
  sSup {ρ : ℝ | ∃ c : Fin m → E3, (∀ i, ‖c i‖ + ρ ≤ 1) ∧ ∀ i j, i ≠ j → 2 * ρ ≤ dist (c i) (c j)}

/-- Density of the best packing of `m` equal balls in a ball. -/
noncomputable def density (m : ℕ) : ℝ := m * r m ^ 3

/-- `m > 1` sets a new density record. -/
def IsRecord (m : ℕ) : Prop := 1 < m ∧ ∀ j, 1 < j → j < m → density j < density m

/-- The terms of A084829 given in the entry. -/
def terms : Finset ℕ :=
  {2, 3, 4, 6, 8, 9, 11, 12, 18, 21, 25, 30, 31, 32, 33, 34, 35, 36, 38, 49, 51, 53, 56, 59,
    60, 61}

theorem main : ∀ m : ℕ, m ≤ 61 → (IsRecord m ↔ m ∈ terms) := by
  sorry

end OMA.S_oeis_a084829
