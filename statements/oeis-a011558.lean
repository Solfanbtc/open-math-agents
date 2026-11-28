import Mathlib

/-!
# A011558: partitions into distinct parts of A084215 are counted by the indicator of 5 ∤ n + 1

Source: https://oeis.org/A011558
Credit: @Solfanbtc

A011558 (offset 0): the expansion of `(x + x^3)/(1 + x + … + x^4)` mod 2; per the entry it is the
characteristic function of the numbers coprime to 5 (`a(0) = 0`), i.e. `a(m) = 1` if `5 ∤ m` and
`a(m) = 0` if `5 ∣ m`. We use this description as the definition. (Checked with python3: the mod-2
expansion of the g.f. agrees with it for `m < 200`.)

A084215 (offset 0): the expansion of `(1 + x^2)/(1 - 2x)`: 1, 2, 5, 10, 20, 40, …, i.e. `1`, `2`
and `5 · 2^(k-2)` for `k ≥ 2` (formula `a(k) = 2 a(k-1)` for `k ≥ 3`, `a(0..2) = 1, 2, 5`).

Conjecture (R. J. Mathar, Mar 01 2023): "a(n+1) is the number of ways of partitioning n into
distinct parts of A084215." `main` states it for every `n ≥ 0`: the number of finite sets of
terms of A084215 with sum `n` is `a(n+1)`. (The terms of A084215 are pairwise distinct, so a
partition into distinct parts is a finite set of terms.) Checked with python3 for `n < 199`.
-/

namespace OMA.S_oeis_a011558

/-- A011558: the characteristic function of the numbers coprime to 5. -/
def a (m : ℕ) : ℕ := if 5 ∣ m then 0 else 1

/-- A084215: `1, 2, 5, 10, 20, 40, …`. -/
def b (k : ℕ) : ℕ := if k = 0 then 1 else if k = 1 then 2 else 5 * 2 ^ (k - 2)

/-- The number of partitions of `n` into distinct parts that are terms of A084215. -/
noncomputable def numPartitions (n : ℕ) : ℕ :=
  {s : Finset ℕ | (∀ x ∈ s, ∃ k, b k = x) ∧ ∑ x ∈ s, x = n}.ncard

/-- Mathar's conjecture: the number of partitions of `n` into distinct parts of A084215 is
`a(n+1)`. -/
theorem main : ∀ n : ℕ, numPartitions n = a (n + 1) := by
  sorry

end OMA.S_oeis_a011558
