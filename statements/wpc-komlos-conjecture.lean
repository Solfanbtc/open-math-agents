import Mathlib

/-!
# Komlós conjecture

Source: https://en.wikipedia.org/wiki/Discrepancy_theory
Credit: @Solfanbtc

The source lists the Komlós conjecture among the unsolved problems of discrepancy theory. The
catalogue states it as follows: there is an absolute constant `K` such that for all vectors
`v₁, …, vₙ` in `ℝᵐ` of Euclidean norm at most `1` there are signs `ε₁, …, εₙ ∈ {-1, 1}` with
`‖ε₁ v₁ + … + εₙ vₙ‖_∞ ≤ K`; the constant does not depend on `m` or `n`. It implies the
Beck–Fiala conjecture, and the best known bounds grow slowly with `n` (Banaszczyk's
`O(√(log n))` and later improvements).

Note for the reviewer: the Wikipedia page of János Komlós phrases the conjecture with unit
vectors and the distance between the sums of the two parts of a partition of the vectors, without
naming the distance. Read with the Euclidean distance that claim is false (for `n` orthonormal
vectors every signed sum has Euclidean norm `√n`), so the distance is the one of the sup norm, as
in the catalogue. Unit vectors or vectors of norm at most `1` give equivalent conjectures; the
statement below follows the catalogue (norm at most `1`).

Encoding: a vector of `ℝᵐ` is a function `Fin m → ℝ`; its Euclidean norm is at most `1` when the
sum of the squares of its coordinates is at most `1`, and the sup norm of the signed sum is at
most `K` when each of its coordinates has absolute value at most `K`.
-/

namespace OMA.S_wpc_komlos_conjecture

/-- **Komlós conjecture**: there is a constant `K` such that for all `m` and `n` and all vectors
`v 0, …, v (n - 1)` of `ℝᵐ` of Euclidean norm at most `1`, some choice of signs `ε i ∈ {1, -1}`
makes every coordinate of `∑ i, ε i • v i` at most `K` in absolute value. -/
theorem main : ∃ K : ℝ, ∀ (m n : ℕ) (v : Fin n → Fin m → ℝ),
    (∀ i, ∑ j, v i j ^ 2 ≤ 1) →
      ∃ ε : Fin n → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∀ j, |∑ i, ε i * v i j| ≤ K := by
  sorry

end OMA.S_wpc_komlos_conjecture
