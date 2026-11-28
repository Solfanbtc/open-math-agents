import Mathlib

/-!
# A023393: Maximal number of circles of radius 1 that can be packed in a circle of radius n.

Source: https://oeis.org/A023393
Credit: @Solfanbtc

Data (offset 0): 0, 1, 2, 7, 11, 19, 27, 38, 50, 64, 80, 98, 118.
"The terms for n>5 are only conjectures supported by extensive computations." The entry claims
these 13 values; stated here as a(n) = data(n) for all n ≤ 12 (the part n ≤ 5 is claimed known).
The EXTENSIONS line reporting that M. Bouayoun suggests the sequence "probably continues 138,
161, ..." is a separate, hedged suggestion and is not included.

Conventions: a packing of `m` unit disks in the disk of radius `n` centered at the origin of the
Euclidean plane is a family of centers `c i` with `‖c i‖ + 1 ≤ n` (each unit disk inside the big
one) and `2 ≤ dist (c i) (c j)` for `i ≠ j` (disjoint interiors). a(n) is the largest such `m`
(the set of such `m` is bounded by an area argument, so `sSup` is the maximum). For n = 0 no unit
disk fits and a(0) = 0, as in the data.
-/

namespace OMA.S_oeis_a023393

/-- Points of the Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- `m` unit disks can be packed in the disk of radius `R` centered at the origin. -/
def Packable (R : ℝ) (m : ℕ) : Prop :=
  ∃ c : Fin m → Pt, (∀ i, ‖c i‖ + 1 ≤ R) ∧ ∀ i j, i ≠ j → 2 ≤ dist (c i) (c j)

/-- A023393: the maximal number of unit circles that can be packed in a circle of radius `n`. -/
noncomputable def a (n : ℕ) : ℕ := sSup {m : ℕ | Packable n m}

/-- The terms given in the entry. -/
def data : List ℕ := [0, 1, 2, 7, 11, 19, 27, 38, 50, 64, 80, 98, 118]

theorem main : ∀ n : ℕ, (h : n < data.length) → a n = data.get ⟨n, h⟩ := by
  sorry

end OMA.S_oeis_a023393
