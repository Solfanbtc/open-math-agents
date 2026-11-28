import Mathlib

/-!
# A053828: Sum of digits of (n written in base 7).

Source: https://oeis.org/A053828
Credit: @Solfanbtc

`s(n) = A053828(n)` is the sum of the base-7 digits of `n` (offset 0): `0, 1, 2, 3, 4, 5, 6, 1, 2, ...`.

Claim (Omar E. Pol, Feb 21 2010, in the entry): it appears that the sequence can be written as a
triangle, row 0 = `s(0)` and row `k ≥ 1` = `s(7^{k-1}), ..., s(7^k - 1)` (Pol's rows
`0 | 1..6 | 1,2,...,12 | ...`), whose rows converge to A173527, where
`A173527(j) = 1 + s(j - 1)` (`j ≥ 1`). Convergence of the rows means: for each `j ≥ 1`, the `j`-th
entry of row `k`, `s(7^{k-1} + j - 1)`, equals `A173527(j)` for all sufficiently large `k`.
(A173527's own comment: `a(n) = A053828(7^k + n - 1)` in the limit `k → ∞`.)

A python3 check: `s(7^k + j - 1) = 1 + s(j - 1)` for all `1 ≤ j < 3000`, `5 ≤ k ≤ 8`.

Conventions: `s n = (Nat.digits 7 n).sum`; "for all sufficiently large `k`" is `∀ᶠ k in atTop`.
-/

namespace OMA.S_oeis_a053828

open Filter

/-- `s n = A053828(n)`: the sum of the base-7 digits of `n`. -/
def s (n : ℕ) : ℕ := (Nat.digits 7 n).sum

/-- `A173527(j) = 1 + s(j - 1)`. -/
def A173527 (j : ℕ) : ℕ := 1 + s (j - 1)

/-- Pol's observation: the rows of the triangle form of A053828 converge to A173527. -/
theorem main : ∀ j : ℕ, 1 ≤ j → ∀ᶠ k in atTop, s (7 ^ (k - 1) + j - 1) = A173527 j := by
  sorry

end OMA.S_oeis_a053828
