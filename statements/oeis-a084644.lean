import Mathlib

/-!
# A084644: Best packings of m>1 equal circles into a larger circle setting a new density record.

Source: https://oeis.org/A084644
Credit: @Solfanbtc

Data: `2, 3, 4, 7, 19, 37, 55, 85, 121, 147, 148, 150, 151, 187, 188, 190, 191, 192, 193, 198`.
The entry says the terms for `n > 5` are only conjectures (those for `n ≤ 5` are proved). The
conjecture is that these are the first 20 terms; `main` states it as: for `2 ≤ m ≤ 198`, `m`
sets a new density record if and only if `m` is one of the listed values.

Conventions.
* `R(m)` is the smallest radius of a circle containing `m` non-overlapping unit circles:
  the infimum of the `r` for which there are centers `c i` in the Euclidean plane with
  `‖c i‖ + 1 ≤ r` and `dist (c i) (c j) ≥ 2` for `i ≠ j` (the infimum is attained by
  compactness, so this is the best packing).
* The density of the best packing of `m` circles is `m / R(m)^2` (area of the circles over the
  area of the container).
* `m > 1` sets a new density record if its density is strictly larger than the density for
  every `j` with `2 ≤ j < m` (so `m = 2` is a record). Example: `a(4) = 7` since
  `7/9 = 0.777...` exceeds `4/(1+√2)^2 = 0.686...` (and the densities for 5, 6).
-/

namespace OMA.S_oeis_a084644

/-- The Euclidean plane. -/
abbrev E := EuclideanSpace ℝ (Fin 2)

/-- `m` unit circles fit, without overlap, in a circle of radius `r` centered at `0`. -/
def Fits (m : ℕ) (r : ℝ) : Prop :=
  ∃ c : Fin m → E, (∀ i, ‖c i‖ + 1 ≤ r) ∧ ∀ i j, i ≠ j → 2 ≤ dist (c i) (c j)

/-- `R(m)`: the radius of the smallest circle containing `m` non-overlapping unit circles. -/
noncomputable def R (m : ℕ) : ℝ := sInf {r : ℝ | Fits m r}

/-- Density of the best packing of `m` equal circles in a circle. -/
noncomputable def density (m : ℕ) : ℝ := m / R m ^ 2

/-- `m > 1` sets a new density record. -/
def IsRecord (m : ℕ) : Prop := 2 ≤ m ∧ ∀ j, 2 ≤ j → j < m → density j < density m

/-- The listed terms of A084644. -/
def terms : List ℕ :=
  [2, 3, 4, 7, 19, 37, 55, 85, 121, 147, 148, 150, 151, 187, 188, 190, 191, 192, 193, 198]

/-- The conjectured first 20 terms: up to 198 the records are exactly the listed values. -/
theorem main : ∀ m : ℕ, 2 ≤ m → m ≤ 198 → (IsRecord m ↔ m ∈ terms) := by
  sorry

end OMA.S_oeis_a084644
