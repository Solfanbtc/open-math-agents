import Mathlib

/-!
# A122537: n^2 divides a(n) only for n = 1, 2, 4, 5, 10

Source: https://oeis.org/A122537
`a(1) = 1`; for `n > 1`, `a(n)` is the smallest number greater than `a(n-1)`, divisible by `n`
and not equal to any `a(i) + a(j)` with `i, j ≤ n-1`: 1, 4, 6, 16, 25, 30, 35, 40, 45, 100, ...
The entry: "Jonathan Vos Post asks if 1, 2, 4 and 5 are the only values of n for which n^2
divides a(n), Sep 19 2006. J. Lowell, Oct 02 2006 remarks that n = 1, 2, 4, 5 and 10 have this
property and conjectures that there are no other values."

We state Lowell's conjecture: for `n ≥ 1`, `n^2 ∣ a(n)` iff `n ∈ {1, 2, 4, 5, 10}`.
Conventions. `i = j` is allowed in `a(i) + a(j)` (the Mathematica program uses `Tuples[s, 2]`,
and the Maple program marks `a(j) + a(n)` for `j ≤ n`, including `2 a(n)`). `terms n` is
`[a(1), ..., a(n)]`; each new term is an `sInf` (it exists: only finitely many sums are
excluded).
Checked with python3: the rule reproduces the 51 listed terms, and among `n ≤ 2500` exactly
`n = 1, 2, 4, 5, 10` have `n^2 ∣ a(n)`.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a122537

/-- `terms n = [a(1), ..., a(n)]`. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | n + 2 =>
    let l := terms (n + 1)
    l ++ [sInf {m : ℕ | l.getLastD 0 < m ∧ (n + 2) ∣ m ∧ ∀ x ∈ l, ∀ y ∈ l, m ≠ x + y}]

/-- A122537: `a(n)`, `n ≥ 1`. -/
noncomputable def a (n : ℕ) : ℕ := (terms n).getD (n - 1) 0

theorem main : ∀ n : ℕ, 1 ≤ n → (n ^ 2 ∣ a n ↔ n ∈ ({1, 2, 4, 5, 10} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a122537
