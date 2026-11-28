import Mathlib

/-!
# A035312: Zorach additive triangle, read by rows.

Source: https://oeis.org/A035312
Credit: @Solfanbtc

The triangle `T(n, k)`, `1 ≤ k ≤ n`: each entry is the sum of its west and northwest neighbours,
`T(n, k) = T(n, k-1) + T(n-1, k-1)` for `k ≥ 2`, and the first entry `T(n, 1)` of each row is the
least positive integer such that no entry of row `n` already occurs in rows `1, …, n-1`.
Rows: `1; 2, 3; 4, 6, 9; 7, 11, 17, 26; 5, 12, 23, 40, 66; …`.
Conjecture (in the entry): the triangle is a permutation of the positive integers.

Conventions:
* Row `n` is `List.scanl (· + ·) s (row (n-1))` with `s = T(n, 1)`; starting from the empty row 0
  with nothing used, this gives row 1 = `[1]`. Entries of a row are strictly increasing (all entries
  are positive), so a row never repeats a number within itself; the only condition is avoiding the
  numbers already used. A valid `s` always exists (anything larger than every used number works);
  the `dite` fallback `0` is never taken. Checked in python: rows 1 to 12 match the data.
* "Permutation of the positive integers": every entry is positive and every positive integer is
  `T(n, k)` for exactly one position `1 ≤ k ≤ n`.
-/

namespace OMA.S_oeis_a035312

open Classical in
/-- One construction step: from the last row `r` and the set `U` of numbers used so far, build
the next row and the new set of used numbers. -/
noncomputable def step (p : List ℕ × Finset ℕ) : List ℕ × Finset ℕ :=
  let s : ℕ :=
    if h : ∃ s : ℕ, 1 ≤ s ∧ ∀ x ∈ List.scanl (· + ·) s p.1, x ∉ p.2 then Nat.find h else 0
  let row := List.scanl (· + ·) s p.1
  (row, p.2 ∪ row.toFinset)

/-- Row `n` of the triangle (row `0` is empty, row `n ≥ 1` has length `n`). -/
noncomputable def row (n : ℕ) : List ℕ := (step^[n] ([], ∅)).1

/-- `T(n, k)` for `1 ≤ k ≤ n`. -/
noncomputable def T (n k : ℕ) : ℕ := (row n).getD (k - 1) 0

/-- The Zorach additive triangle is a permutation of the positive integers. -/
theorem main : (∀ n k : ℕ, 1 ≤ k → k ≤ n → 1 ≤ T n k) ∧
    ∀ m : ℕ, 1 ≤ m → ∃! p : ℕ × ℕ, 1 ≤ p.2 ∧ p.2 ≤ p.1 ∧ T p.1 p.2 = m := by
  sorry

end OMA.S_oeis_a035312
