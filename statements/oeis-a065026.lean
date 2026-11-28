import Mathlib

/-!
# A065026: smallest number that is not a sum or product of a subset of the earlier terms

Source: https://oeis.org/A065026
Credit: @Solfanbtc

`a(1) = 1`; for `n > 1`, `a(n)` is the smallest (positive) number that is not the sum or the
product of any (nonempty) subset of `a(1), …, a(n-1)`: `1, 2, 4, 9, 17, 25, 59, 67, …` (e.g.
`a(4) = 9`: sums and products of subsets of `{1, 2, 4}` give `1, …, 8`). Below `terms k` lists
`a(1), …, a(k+1)`, a subset is a sublist (the terms are distinct), and `a 0 = 0` (offset 1). A
simulation with this definition gives the first 20 data terms.

Conjectures (Colin Barker, Jun 19 2019, OEIS formulas), both stated:
1. G.f.: `x(1 - x)(1 + 3x + 5x^2 + 10x^3 + 15x^4 + 14x^5 + 25x^6 + 10x^7 + 8x^8 + 18x^9 + 42x^10
   - 402x^12 - 552x^13 - 720x^14 - 804x^15)/(1 - 2x^2 - 4x^4 + 2x^6)`, stated with the denominator
   cleared (it is a unit in `ℚ⟦x⟧`), for `∑_{n ≥ 1} a(n) x^n`.
2. `a(n) = 2a(n-2) + 4a(n-4) - 2a(n-6)` for `n > 17`.
(Python: both agree with all 38 data terms.)
-/

namespace OMA.S_oeis_a065026

open PowerSeries

/-- The next term after the list `l` of earlier terms. -/
noncomputable def next (l : List ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ ∀ s ∈ l.sublists, s ≠ [] → m ≠ s.sum ∧ m ≠ s.prod}

/-- `terms k = [a(1), …, a(k+1)]`. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => [1]
  | k + 1 => terms k ++ [next (terms k)]

/-- A065026 (offset 1; `a 0 = 0`). -/
noncomputable def a (n : ℕ) : ℕ := if n = 0 then 0 else (terms (n - 1)).getD (n - 1) 0

/-- Barker's conjectured g.f. and recurrence. -/
theorem main :
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 2 * X ^ 2 - 4 * X ^ 4 + 2 * X ^ 6) =
      X * (1 - X) * (1 + 3 * X + 5 * X ^ 2 + 10 * X ^ 3 + 15 * X ^ 4 + 14 * X ^ 5 + 25 * X ^ 6 +
        10 * X ^ 7 + 8 * X ^ 8 + 18 * X ^ 9 + 42 * X ^ 10 - 402 * X ^ 12 - 552 * X ^ 13 -
        720 * X ^ 14 - 804 * X ^ 15)) ∧
    (∀ n : ℕ, 17 < n →
      (a n : ℤ) = 2 * a (n - 2) + 4 * a (n - 4) - 2 * a (n - 6)) := by
  sorry

end OMA.S_oeis_a065026
