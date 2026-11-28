import Mathlib

/-!
# A006950: G.f.: Product_{k>=1} (1 + x^(2*k - 1)) / (1 - x^(2*k)).

Source: https://oeis.org/A006950
Credit: @Solfanbtc

Conjecture of Omar E. Pol (Oct 09 2011): A006950 is 1 together with the row sums of the
triangle A195836, also column 1 of A195836, also column 2 of the square array A195825.

Conventions, taken from the cited entries:
* `tri j = j * (j + 1) / 2` (A000217): for `j ≥ 1` these are the nonzero generalized
  hexagonal numbers 1, 3, 6, 10, ..., used by A195826 and by column 2 of A195825.
* `sgn j = A057077(j - 1)`, the period-4 signs `+1, +1, -1, -1, ...` for `j = 1, 2, 3, 4, ...`.
* A195836 "arises from A195826 in the same way as A175003 arises from A195310", and
  A175003 is given by `T(n,k) = A057077(k-1) * A000041(A195310(n,k))`. So A195836 is
  `T(n,k) = sgn k * a (n - tri k)` for `n ≥ 1`, `k ≥ 1`, `tri k ≤ n`; row `n` has its
  entries for `k ∈ [1, n]` with `tri k ≤ n` (the bound `k ≤ n` follows from `tri k ≤ n`).
  This matches the OEIS data of A195836 (checked against the first 18 rows).
* Column 2 of A195825 is the GW-BASIC recursion in that entry: `T(0) = 1` and, for `n ≥ 1`,
  `T(n) = Σ_{j=1..n, tri j ≤ n} sgn j * T(n - tri j)`. In the definition below
  `n + 1 - tri (j + 1)` is written as `n - (tri (j + 1) - 1)` (equal, since `tri (j+1) ≥ 1`)
  so that termination is evident.
* `a n` is the coefficient of `x^n` in the generating function. Only the factors with
  `2k - 1 ≤ n` affect that coefficient, so the product is truncated to `k ≤ n + 1`;
  `1 / (1 - x^(2k))` is written as the power series `Σ_m x^(2k m)`.

"1 together with the row sums" means `a 0 = 1` and `a n` is the sum of row `n` for `n ≥ 1`;
"column 1" means `a (n - 1) = T(n, 1)` for every row `n ≥ 1` (column 1 starts at row 1).
The values were checked in Python for `n ≤ 60` against the OEIS data.
-/

open PowerSeries Finset

namespace OMA.S_oeis_a006950

/-- The `k`-th factor (`k ≥ 1`) `(1 + x^(2k-1)) / (1 - x^(2k))` of the generating function. -/
noncomputable def factor (k : ℕ) : PowerSeries ℤ :=
  (1 + X ^ (2 * k - 1)) * PowerSeries.mk (fun m => if 2 * k ∣ m then 1 else 0)

/-- A006950: the coefficient of `x^n` in `∏_{k ≥ 1} (1 + x^(2k-1)) / (1 - x^(2k))`. -/
noncomputable def a (n : ℕ) : ℤ :=
  PowerSeries.coeff n (∏ k ∈ Icc 1 (n + 1), factor k)

/-- Triangular numbers A000217 (the generalized hexagonal numbers). -/
def tri (j : ℕ) : ℕ := j * (j + 1) / 2

/-- `A057077(j - 1)`: the signs `1, 1, -1, -1, 1, 1, ...` for `j = 1, 2, 3, ...`. -/
def sgn (j : ℕ) : ℤ := if (j - 1) % 4 < 2 then 1 else -1

/-- The triangle A195836: `T(n,k) = A057077(k-1) * A006950(n - A000217(k))`. -/
noncomputable def triangle (n k : ℕ) : ℤ := sgn k * a (n - tri k)

/-- Sum of row `n` of A195836: the entries with `1 ≤ k ≤ n` and `tri k ≤ n`. -/
noncomputable def rowSum (n : ℕ) : ℤ :=
  ∑ k ∈ (Icc 1 n).filter (fun k => tri k ≤ n), triangle n k

/-- Column 2 of the square array A195825 (generalized hexagonal numbers). -/
def colTwo : ℕ → ℤ
  | 0 => 1
  | n + 1 => ∑ j : Fin (n + 1),
      if tri (j.val + 1) ≤ n + 1 then sgn (j.val + 1) * colTwo (n - (tri (j.val + 1) - 1))
      else 0

/-- Pol's conjecture: A006950 is 1 followed by the row sums of A195836, is column 1 of
A195836, and is column 2 of A195825. -/
theorem main :
    a 0 = 1 ∧ (∀ n, 1 ≤ n → a n = rowSum n) ∧
    (∀ n, 1 ≤ n → a (n - 1) = triangle n 1) ∧
    (∀ n, a n = colTwo n) := by
  sorry

end OMA.S_oeis_a006950
