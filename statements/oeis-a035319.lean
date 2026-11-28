import Mathlib

/-!
# A035319: Number of rooted maps of genus n with one vertex and one face; the maps are considered on orientable surfaces and contain 2n edges

Source: https://oeis.org/A035319
Credit: @Solfanbtc

Conjecture (Eric M. Rains, Jan 24 2006): `a(n) = (4n)! / (2^(2n) (2n+1)!) = (4n-1)!!/(2n+1)`.

Model. A rooted map with one vertex and `2n` edges has `4n` darts; numbering them
`0, ..., 4n-1` counterclockwise around the vertex starting from the root, the vertex rotation is
`finRotate (4n)` (`j ↦ j + 1 mod 4n`) and the map is given by its edge involution `α`, a
fixed-point-free involution of the darts. This is a bijection between rooted one-vertex maps
with `2n` edges and such `α`. The faces are the cycles of `finRotate (4n) * α`; the map has one
face iff that permutation is a single `4n`-cycle. Euler's formula `V - E + F = 2 - 2g` with
`V = F = 1`, `E = 2n` gives genus `g = n` automatically, so `a(n)` counts these `α`.
Checked by brute force (python3): `1, 21, 1485` for `n = 1, 2, 3`, as in the data.

Minimal fix: for `n = 0` the map is the single vertex on the sphere with no darts, one face by
convention, while the permutation model has no darts and no cycle; so `main` is stated for
`n ≥ 1`. The division is exact; it is stated as `a(n) * (2^(2n) (2n+1)!) = (4n)!`.
-/

namespace OMA.S_oeis_a035319

/-- Edge involutions of rooted one-vertex maps with `2n` edges that have exactly one face. -/
def oneFaceMaps (n : ℕ) : Finset (Equiv.Perm (Fin (4 * n))) :=
  Finset.univ.filter fun α =>
    α * α = 1 ∧ (∀ j, α j ≠ j) ∧ (finRotate (4 * n) * α).cycleType = {4 * n}

/-- A035319(n), for `n ≥ 1`. -/
def a (n : ℕ) : ℕ := (oneFaceMaps n).card

/-- Rains's conjecture: `a(n) = (4n)! / (2^(2n) (2n+1)!)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    a n * (2 ^ (2 * n) * (2 * n + 1).factorial) = (4 * n).factorial := by
  sorry

end OMA.S_oeis_a035319
