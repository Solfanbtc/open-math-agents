import Mathlib

/-!
# A026596: Row sums of A026584.

Source: https://oeis.org/A026596
Credit: @Solfanbtc

A026584 is the irregular triangle `T(i, j)`, `0 ≤ j ≤ 2i`: `T(i, 0) = T(i, 2i) = 1`;
`T(i, 1) = T(i, 2i-1) = ⌊i/2⌋` (`i ≥ 1`); and for `i ≥ 2`, `2 ≤ j ≤ 2i-2`:
`T(i, j) = T(i-1, j-2) + T(i-1, j-1) + T(i-1, j)` if `i + j` is odd,
`T(i, j) = T(i-1, j-2) + T(i-1, j)` if `i + j` is even.
A026596 (offset 0) is `a(n) = ∑_{k=0}^{n} T(n, k)`, as in the entry's formula and Mathematica
program (the sum runs over `k ≤ n` only, not over the whole row): `1, 1, 4, 8, 23, 54, 143, ...`.

Conjecture (R. J. Mathar, Jun 23 2013, in the entry):
`n a(n) - 3(n-1) a(n-1) - (5n-6) a(n-2) + 3(5n-13) a(n-3) + 2(4n-9) a(n-4) - 8(2n-9) a(n-5) = 0`,
stated for all `n ≥ 5` (where `a(n-5)` is defined).

A python3 check: the definition reproduces the data of A026584 and A026596, and the recurrence
holds for all `5 ≤ n < 300`. The Lean kernel (`decide`) confirms `a 0, ..., a 11` against the
data.

Conventions:
* `row i` is the list `[T(i, 0), ..., T(i, 2i)]`, built from `row (i-1)`. For `i = 1` the rules
  give `[1, 0, 1]` (`T(1,1) = ⌊1/2⌋ = 0`).
* The recurrence is stated in `ℤ`.
-/

namespace OMA.S_oeis_a026596

/-- `row i = [T(i, 0), ..., T(i, 2i)]` for A026584. -/
def row : ℕ → List ℕ
  | 0 => [1]
  | i + 1 =>
      let P := row i
      (List.range (2 * (i + 1) + 1)).map fun j =>
        if j = 0 ∨ j = 2 * (i + 1) then 1
        else if j = 1 ∨ j = 2 * (i + 1) - 1 then (i + 1) / 2
        else if (i + 1 + j) % 2 = 0 then P.getD (j - 2) 0 + P.getD j 0
        else P.getD (j - 2) 0 + P.getD (j - 1) 0 + P.getD j 0

/-- `a n = A026596(n) = ∑_{k=0}^{n} T(n, k)`. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), ((row n).getD k 0 : ℤ)

/-- Mathar's conjectured recurrence, for all `n ≥ 5`. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    (n : ℤ) * a n - 3 * ((n : ℤ) - 1) * a (n - 1) - (5 * (n : ℤ) - 6) * a (n - 2)
      + 3 * (5 * (n : ℤ) - 13) * a (n - 3) + 2 * (4 * (n : ℤ) - 9) * a (n - 4)
      - 8 * (2 * (n : ℤ) - 9) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a026596
