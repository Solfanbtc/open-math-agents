import Mathlib

/-!
# A006343: Arkons: number of elementary maps with n-1 nodes.

Source: https://oeis.org/A006343
Credit: @Solfanbtc

`a(n)` (offset 0): `1, 0, 1, 1, 4, 10, 34, 112, 398, 1443, ...`. The sequence is taken from the
entry's explicit formula (its Maple and Mathematica programs, which produce the data):
`a(0) = 1` and, for `n ≥ 1`,
`a(n) = ∑_{k=0}^{⌊(n-2)/2⌋} C(n, k) · C(2n - 3k - 4, n - 2k - 2) / (n - k - 1)`
(empty sum `0` for `n = 1`).

Conjecture (R. J. Mathar, Feb 20 2020, in the entry): `a` is D-finite with recurrence
`-(n+3)(n-1) a(n) + (11n² - 2n - 45) a(n-1) - (37n + 29)(n-3) a(n-2)
 + (29n² - 125n + 78) a(n-3) + (61n - 106)(n-3) a(n-4) - 155 (n-3)(n-4) a(n-5) = 0`,
stated for every `n ≥ 5` (the smallest `n` for which all of `a(n-5), ..., a(n)` are defined).

A python3 check (exact rationals): the formula reproduces the 27 data terms, every value is an
integer, and the recurrence holds for all `5 ≤ n < 400`. In Lean, `simp`/`norm_num` confirm
`a 1 = 0`, `a 7 = 112`, `a 9 = 1443` for this definition.

Conventions:
* `a` is computed in `ℚ` (the individual summands need not be integers). For `k ≤ ⌊(n-2)/2⌋`
  all binomial arguments are nonnegative, so natural-number binomials are used.
-/

namespace OMA.S_oeis_a006343

/-- `a n = A006343(n)`, from the entry's explicit formula. -/
def a (n : ℕ) : ℚ :=
  if n = 0 then 1 else
    ∑ k ∈ Finset.range ((n - 2) / 2 + 1),
      if n < 2 then 0 else
        ((n.choose k : ℚ) * ((2 * n - 3 * k - 4).choose (n - 2 * k - 2) : ℚ)) /
          ((n : ℚ) - k - 1)

/-- Mathar's conjectured D-finite recurrence, for all `n ≥ 5`. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    -((n : ℚ) + 3) * ((n : ℚ) - 1) * a n
      + (11 * (n : ℚ) ^ 2 - 2 * n - 45) * a (n - 1)
      - (37 * (n : ℚ) + 29) * ((n : ℚ) - 3) * a (n - 2)
      + (29 * (n : ℚ) ^ 2 - 125 * n + 78) * a (n - 3)
      + (61 * (n : ℚ) - 106) * ((n : ℚ) - 3) * a (n - 4)
      - 155 * ((n : ℚ) - 3) * ((n : ℚ) - 4) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a006343
