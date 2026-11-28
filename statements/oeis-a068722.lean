import Mathlib

/-!
# A068722: Solenoidal flows in a 3 × 3 square array with velocities -n..n

Source: https://oeis.org/A068722
Credit: @Solfanbtc

A068722 (offset 0): `1, 35, 247, 925, 2501, …`, with the OEIS formula
`a(n) = (1 + 2n + 2n^2)(1 + 3n + 3n^2)`, used here as the definition.

A255437 (offset 1): "in positive integers: replace `k^2` with the first `k` odd numbers":
`1, 2, 3, 1, 3, 5, 6, 7, 8, 1, 3, 5, 10, …` (`1 → 1`; `4 → 1, 3`; `9 → 1, 3, 5`; …). Below,
`prefix M` is the concatenation of the blocks of `1, …, M`; since every block is nonempty,
`prefix i` has at least `i` terms, and `A255437(i)` is its `i`-th term.

Conjecture (Reinhard Zumkeller, Mar 23 2015, OEIS comment): "`A255437(a(n)) = 2n+1`, i.e. `a(n)`
gives the position of the first occurrence of `2n+1` in A255437."

Minimal fix: as written this fails at `n = 1` (`A255437(35) = 9`, and `3` first occurs at position
`3`). The companion comment in A255437 (same author) reads `a(A068722(n)) = (2n+1)^2`, "the
position of the first occurrence of the n-th odd square", and that is what the data show:
`A255437(A068722(n)) = 1, 9, 25, 49, …` and the first occurrences of `(2n+1)^2` are at
`1, 35, 247, 925, 2501, 5551, 10795, 19097` (Python). The conjecture is stated with `(2n+1)^2`.
-/

namespace OMA.S_oeis_a068722

/-- A068722: `a(n) = (1 + 2n + 2n^2)(1 + 3n + 3n^2)`. -/
def a (n : ℕ) : ℕ := (1 + 2 * n + 2 * n ^ 2) * (1 + 3 * n + 3 * n ^ 2)

/-- The block replacing `m`: the first `k` odd numbers if `m = k^2`, else `[m]`. -/
def block (m : ℕ) : List ℕ :=
  if (Nat.sqrt m) ^ 2 = m then (List.range (Nat.sqrt m)).map (fun i => 2 * i + 1) else [m]

/-- The terms coming from `1, …, M`. -/
def prefixTerms (M : ℕ) : List ℕ := (List.range M).flatMap fun i => block (i + 1)

/-- A255437 (offset 1). -/
def A255437 (i : ℕ) : ℕ := (prefixTerms i).getD (i - 1) 0

/-- Zumkeller's conjecture (with `(2n+1)^2`): `a(n)` is the position of the first occurrence of
`(2n+1)^2` in A255437. -/
theorem main : ∀ n : ℕ, A255437 (a n) = (2 * n + 1) ^ 2 ∧
    ∀ j : ℕ, 1 ≤ j → j < a n → A255437 j ≠ (2 * n + 1) ^ 2 := by
  sorry

end OMA.S_oeis_a068722
