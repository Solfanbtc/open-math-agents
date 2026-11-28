import Mathlib

/-!
# A059774: lattice points near the segment from the origin to `(1, 2, 3, …, n)`

Source: https://oeis.org/A059774
Credit: @Solfanbtc

In `ℝⁿ` take the line segment from the origin to `P = (1, 2, 3, …, n)`; let `d` be the squared
distance to it from the closest point of `ℤⁿ`, excluding the endpoints. `a(n) = d · (P·P)`
(offset `n = 2`). The entry gives the terms `1, 3, 9, 21, 40, 75, 120, 189` for `n = 2, …, 9` and
states: for `n ≥ 10`, `a(n) = A000330(n-1) = 1² + 2² + ⋯ + (n-1)²`; it adds "Officially these are
just conjectures so far". We state both the listed small values and the formula for `n ≥ 10`.

Reading: Euclidean distance from a lattice point to the closed segment `[0, P]`, minimized over
lattice points other than `0` and `P`. (Using the distance to the whole line instead, over lattice
points not on it, gives the same minimum: `e_n` already gives `d · P·P = P·P - n² < P·P`, and a
point whose projection falls outside the segment is at squared distance `≥ 1` from it.)
A python3 brute force over `{-1, …, n+1}ⁿ` reproduces `1, 3, 9, 21, 40, 75` for `n = 2, …, 7`.
-/

namespace OMA.S_oeis_a059774

/-- The point `P = (1, 2, …, n)`. -/
noncomputable def P (n : ℕ) : EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm fun i => ((i : ℕ) + 1 : ℝ)

/-- The integer point `x` as a point of `ℝⁿ`. -/
noncomputable def pt {n : ℕ} (x : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm fun i => (x i : ℝ)

/-- `d`: least squared distance from a non-endpoint lattice point to the segment `[0, P]`. -/
noncomputable def d (n : ℕ) : ℝ :=
  sInf {r : ℝ | ∃ x : Fin n → ℤ, pt x ≠ 0 ∧ pt x ≠ P n ∧
    r = Metric.infDist (pt x) (segment ℝ 0 (P n)) ^ 2}

/-- `a(n) = d · (P·P)`. -/
noncomputable def a (n : ℕ) : ℝ := d n * ‖P n‖ ^ 2

/-- The listed terms for `2 ≤ n ≤ 9`, and `a(n) = ∑_{i < n} i²` for `n ≥ 10`. -/
theorem main :
    (a 2 = 1 ∧ a 3 = 3 ∧ a 4 = 9 ∧ a 5 = 21 ∧ a 6 = 40 ∧ a 7 = 75 ∧ a 8 = 120 ∧ a 9 = 189) ∧
    ∀ n : ℕ, 10 ≤ n → a n = ∑ i ∈ Finset.range n, ((i : ℝ)) ^ 2 := by
  sorry

end OMA.S_oeis_a059774
