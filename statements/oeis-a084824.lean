import Mathlib

/-!
# A084824: Maximum number of unit-diameter spheres packed in a cube of volume n.

Source: https://oeis.org/A084824
Credit: @Solfanbtc

a(n) = maximum number of spheres of diameter one that can be packed in a cube of volume n
(edge length n^(1/3)), n ≥ 1. The entry: "Higher sequence terms are only conjectures found by
numerical experimentation" (it does not say from which n on). Stated: all 34 listed terms
1, 1, 1, 2, 4, 4, 5, 8, 8, 8, 9, 9, 10, 11, 14, 14, 14, 15, 18, 18, 19, 19, 21, 21, 23, 24,
27, 27, 27, 27, 32, 32, 32, 33 (n = 1..34) are the true maxima; this contains the conjectured
higher terms and the established lower ones.

Conventions.
* A packing of m spheres of diameter 1 (radius 1/2) in the cube [0, s]^3, s = n^(1/3), is given
  by centers c_1, ..., c_m ∈ ℝ^3 with every coordinate in [1/2, s - 1/2] (the spheres lie in
  the cube) and pairwise distances ≥ 1 (disjoint interiors). a(n) = L means L is the greatest
  m for which a packing exists.
-/

namespace OMA.S_oeis_a084824

/-- The listed terms, a(n) = data.getD (n - 1) 0. -/
def data : List ℕ :=
  [1, 1, 1, 2, 4, 4, 5, 8, 8, 8, 9, 9, 10, 11, 14, 14, 14, 15, 18, 18, 19, 19, 21, 21, 23, 24,
    27, 27, 27, 27, 32, 32, 32, 33]

/-- m unit-diameter spheres can be packed in a cube of edge s. -/
def CanPack (s : ℝ) (m : ℕ) : Prop :=
  ∃ c : Fin m → EuclideanSpace ℝ (Fin 3),
    (∀ i k, (c i) k ∈ Set.Icc (1 / 2 : ℝ) (s - 1 / 2)) ∧ ∀ i j, i ≠ j → 1 ≤ dist (c i) (c j)

theorem main : ∀ n : ℕ, 1 ≤ n → n ≤ 34 →
    IsGreatest {m : ℕ | CanPack ((n : ℝ) ^ ((1 : ℝ) / 3)) m} (data.getD (n - 1) 0) := by
  sorry

end OMA.S_oeis_a084824
