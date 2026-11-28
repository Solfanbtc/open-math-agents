import Mathlib

/-!
# A084618: Maximum number of circles of area 1 that can be packed in a circle of area n.

Source: https://oeis.org/A084618
Credit: @Solfanbtc

The entry gives a(1..74) = 1, 1, 1, 2, 3, 4, 4, 5, 7, 7, ..., 56, 57, 58, 59 and says: "For most
values of n these are only conjectures, supported by numerical results." It does not say which
values are proved, so the claim is stated for the whole data: a(n) = data(n) for 1 ≤ n ≤ 74.

Conventions: a packing of `m` circles of area 1 (radius `ρ = sqrt(1/π)`) in the circle of area `n`
(radius `R = sqrt(n/π)`, centered at the origin of the Euclidean plane) is a family of centers
`c i` with `‖c i‖ + ρ ≤ R` (each small disk inside the big one) and `2ρ ≤ dist (c i) (c j)` for
`i ≠ j` (disjoint interiors). a(n) is the largest such `m` (bounded by area, so `sSup` is the
maximum). EXAMPLE: a(4) = 2 and a(9) = 7. At squares the data agree with A023393
(a(k^2) = A023393(k) for k ≤ 8), as they must by scaling.
-/

namespace OMA.S_oeis_a084618

open Real

/-- Points of the Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- `m` disks of radius `ρ` can be packed in the disk of radius `R` centered at the origin. -/
def Packable (R ρ : ℝ) (m : ℕ) : Prop :=
  ∃ c : Fin m → Pt, (∀ i, ‖c i‖ + ρ ≤ R) ∧ ∀ i j, i ≠ j → 2 * ρ ≤ dist (c i) (c j)

/-- A084618: maximum number of circles of area 1 that can be packed in a circle of area `n`. -/
noncomputable def a (n : ℕ) : ℕ := sSup {m : ℕ | Packable (√(n / π)) (√(1 / π)) m}

/-- The terms a(1), a(2), ..., a(74) given in the entry. -/
def data : List ℕ :=
  [1, 1, 1, 2, 3, 4, 4, 5, 7, 7, 8, 8, 8, 9, 10, 11, 12, 13, 14, 14, 15, 16, 17, 19, 19, 19, 20,
    21, 21, 22, 23, 24, 24, 26, 27, 27, 28, 29, 30, 31, 31, 32, 33, 34, 35, 37, 37, 37, 38, 39,
    40, 40, 41, 42, 42, 43, 44, 45, 46, 47, 48, 48, 49, 50, 51, 52, 53, 55, 55, 55, 56, 57, 58, 59]

theorem main : ∀ i : ℕ, (h : i < data.length) → a (i + 1) = data.get ⟨i, h⟩ := by
  sorry

end OMA.S_oeis_a084618
