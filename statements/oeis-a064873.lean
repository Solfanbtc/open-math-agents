import Mathlib

/-!
# A064873: First of four sequences representing the lexicographical minimal decomposition of n in 4 squares.

Source: https://oeis.org/A064873
Credit: @Solfanbtc

For `n ≥ 0`, `n = A064873(n)^2 + A064874(n)^2 + A064875(n)^2 + A064876(n)^2`, where
`(A064873(n), A064874(n), A064875(n), A064876(n))` is the lexicographically least among the
decompositions `n = w^2 + x^2 + y^2 + z^2` with `0 ≤ w ≤ x ≤ y ≤ z` (the entries' examples:
for `25`, `(0, 0, 0, 5) < (0, 0, 3, 4) < (1, 2, 2, 4)`; for `19`, `(0, 1, 3, 3) < (1, 1, 1, 4)`).
Such decompositions exist by Lagrange's four-square theorem.

Conjecture (Zhuorui He, Oct 23 2025, in the entry): `A064873(n) = A064874(n - A064874(n)^2)`.
(`A064874(n)^2 ≤ n`, so the argument is a natural number.)

A python3 check: the definitions below reproduce the data of A064873, A064874, A064875 and
A064876, and the conjecture holds for `0 ≤ n < 20000`.

Conventions: lexicographic minimality, coordinate by coordinate: `first n` is the least `w`
occurring in such a decomposition, `second n` the least `x` occurring together with
`w = first n` (`sInf` of nonempty sets).
-/

namespace OMA.S_oeis_a064873

/-- `A064873(n)`: the least `w` with `n = w^2 + x^2 + y^2 + z^2`, `w ≤ x ≤ y ≤ z`. -/
noncomputable def first (n : ℕ) : ℕ :=
  sInf {w : ℕ | ∃ x y z : ℕ, w ≤ x ∧ x ≤ y ∧ y ≤ z ∧ w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = n}

/-- `A064874(n)`: the least `x` with `n = w^2 + x^2 + y^2 + z^2`, `w = A064873(n) ≤ x ≤ y ≤ z`. -/
noncomputable def second (n : ℕ) : ℕ :=
  sInf {x : ℕ | ∃ y z : ℕ, first n ≤ x ∧ x ≤ y ∧ y ≤ z ∧
    (first n) ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = n}

/-- He's conjecture: `A064873(n) = A064874(n - A064874(n)^2)`. -/
theorem main : ∀ n : ℕ, first n = second (n - second n ^ 2) := by
  sorry

end OMA.S_oeis_a064873
