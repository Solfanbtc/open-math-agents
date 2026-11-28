import Mathlib

/-!
# A269526: an infinite Sudoku-type array

Square array `T(n,k)` (`n ≥ 1`, `k ≥ 1`) read by antidiagonals upwards in which each term is the
least positive integer satisfying the condition that no row, column, diagonal, or antidiagonal
contains a repeated term.

Source: https://oeis.org/A269526
Credit: @Solfanbtc

Two conjectures of the entry are stated, as a conjunction:

* (Columns; Bob Selcoe, Jun 29 2016.) Column 1 has constant first differences `+1`, column 2 has
  4-periodic first differences, column 3 16-periodic ones (after the second term). "I conjecture
  that other similar cyclical difference patterns should hold for any column k ..., so that each
  column is a permutation." Stated here as: for every column `k`, the first differences
  `T(n+1,k) - T(n,k)` are eventually periodic. (That each column is a permutation is proved in the
  entry, Theorem C. Selcoe's further guess "Perhaps the cycle lengths are 4^(k-1)" is marked
  "WARNING: These comments may be wrong" and contradicted by M. F. Hasler, Sep 26 2022, who
  observes period 16 for columns 4..9; it is not stated.)
* (Diagonals; N. J. A. Sloane, Jul 02 2016.) "Presumably every diagonal is also a permutation of
  the natural numbers": every diagonal of slope `-1`, i.e. the cells `(n₀ + i, k₀ + i)`, `i ≥ 0`,
  starting from a cell `(n₀, k₀)` of the first row or first column, takes every positive integer
  exactly once.

The array is characterized by the greedy rule (`IsA269526`): the cells are filled in the order
of the antidiagonals `n + k = 2, 3, ...`, each one read upwards (from `(s-1, 1)` to `(1, s-1)`),
and each cell gets the least positive integer that differs from every earlier cell in the same
row, column, diagonal (`n - k` constant) or antidiagonal (`n + k` constant). This determines `T`
uniquely, so the conjecture is stated for every `T` obeying the rule. A python computation of
the first 700 antidiagonals reproduces the rows in the entry, finds the column differences
periodic with periods 1, 4, 16, 16, 16, 16, 16, 16 for columns 1..8 (from terms 1, 1, 2, 8, 17,
52, 91, 92), and finds every number below 200 on the diagonals tested.
-/

namespace OMA.S_oeis_a269526

/-- Cell `(n', k')` is filled before cell `(n, k)`: an earlier antidiagonal, or the same
antidiagonal but lower (antidiagonals are read upwards). -/
def Before (n' k' n k : ℕ) : Prop :=
  n' + k' < n + k ∨ (n' + k' = n + k ∧ n < n')

/-- Cells `(n', k')` and `(n, k)` share a row, column, diagonal or antidiagonal. -/
def SameLine (n' k' n k : ℕ) : Prop :=
  n' = n ∨ k' = k ∨ n' + k' = n + k ∨ (n' : ℤ) - k' = (n : ℤ) - k

/-- `T` is the array A269526: each cell `(n, k)` with `n, k ≥ 1` holds the least positive
integer not already used in an earlier cell on the same line. -/
def IsA269526 (T : ℕ → ℕ → ℕ) : Prop :=
  ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
    1 ≤ T n k ∧
    (∀ n' k', 1 ≤ n' → 1 ≤ k' → Before n' k' n k → SameLine n' k' n k → T n' k' ≠ T n k) ∧
    (∀ m, 1 ≤ m → m < T n k →
      ∃ n' k', 1 ≤ n' ∧ 1 ≤ k' ∧ Before n' k' n k ∧ SameLine n' k' n k ∧ T n' k' = m)

/-- Selcoe's conjecture: in every column the first differences are eventually periodic. -/
def ColumnsConjecture (T : ℕ → ℕ → ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ p : ℕ, 0 < p ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    (T (n + p + 1) k : ℤ) - T (n + p) k = (T (n + 1) k : ℤ) - T n k

/-- Sloane's conjecture: every diagonal is a permutation of the positive integers. -/
def DiagonalsConjecture (T : ℕ → ℕ → ℕ) : Prop :=
  ∀ n₀ k₀ : ℕ, 1 ≤ n₀ → 1 ≤ k₀ → (n₀ = 1 ∨ k₀ = 1) →
    Function.Injective (fun i : ℕ => T (n₀ + i) (k₀ + i)) ∧
    ∀ m : ℕ, 1 ≤ m → ∃ i : ℕ, T (n₀ + i) (k₀ + i) = m

theorem main : ∀ T : ℕ → ℕ → ℕ, IsA269526 T → ColumnsConjecture T ∧ DiagonalsConjecture T := by
  sorry

end OMA.S_oeis_a269526
