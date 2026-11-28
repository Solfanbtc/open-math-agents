import Mathlib

/-!
# A259934: uniqueness of the infinite sequence with a(0) = 0 and a(k) - d(a(k)) = a(k-1)

Source: https://oeis.org/A259934
Credit: @Solfanbtc

A259934 (M. Alekseyev): the infinite sequence starting with `a(0) = 0` such that
`A049820(a(k)) = a(k-1)` for all `k ≥ 1`, where `A049820(n) = n - d(n)` and `d(n)` (A000005) is
the number of divisors of `n`. Data 0, 2, 6, 12, 18, 22, 30, …

The entry says: "V. S. Guba (2015) proved that such an infinite sequence exists. Numerical
evidence suggests that it may also be unique -- is it? All terms below 10^10 are defined
uniquely."

`main` states existence (Guba) together with the open uniqueness: there is exactly one sequence
`b : ℕ → ℕ` with `b 0 = 0` and `b k - d(b k) = b (k-1)` for all `k ≥ 1`.

Conventions. A049820 has offset 1, so every term `b k` with `k ≥ 1` is required to be positive.
(Without this, Mathlib's `Nat.divisors 0 = ∅` would make the constant sequence `0` a spurious
solution.) For `n ≥ 1`, `d(n) ≤ n`, so the subtraction in `ℕ` does not truncate. Finitely many
steps are not unique (e.g. `a(1)` could be `1` or `2`, as `1 - d(1) = 2 - d(2) = 0`); the
question is whether only one branch continues forever. Checked with python3 that the listed
data satisfy the relation.
-/

namespace OMA.S_oeis_a259934

/-- `b` is an infinite sequence with `b 0 = 0` and `A049820(b k) = b (k-1)` for all `k ≥ 1`. -/
def IsChain (b : ℕ → ℕ) : Prop :=
  b 0 = 0 ∧ ∀ k : ℕ, 0 < b (k + 1) ∧ b (k + 1) - (b (k + 1)).divisors.card = b k

/-- Existence (Guba 2015) and the conjectured uniqueness of the sequence A259934. -/
theorem main : ∃! b : ℕ → ℕ, IsChain b := by
  sorry

end OMA.S_oeis_a259934
