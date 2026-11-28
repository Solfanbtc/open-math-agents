import Mathlib

/-!
# A005559: Number of walks on square lattice. Column y=1 of A052174.

Source: https://oeis.org/A005559
Credit: @Solfanbtc

`a(n)` (offset 1): `1, 2, 8, 20, 75, 210, 784, ...`, given by Paul D. Hanna's formula in the entry
(the Maple program runs it for `n = 1..30`):
`a(n) = C(n+1, ⌈(n-1)/2⌉) C(n, ⌊(n-1)/2⌋) - C(n+1, ⌈(n-2)/2⌉) C(n, ⌊(n-2)/2⌋)`
(for `n = 1` the second product is `0`, since `⌊-1/2⌋ = -1`).

Conjecture (R. J. Mathar, Apr 02 2017, in the entry):
`-(n-1)(2n+1)(n+4)(n+3) a(n) + 4(n+1)(2n² + 4n + 9) a(n-1) + 16n(n-1)(2n+3)(n+1) a(n-2) = 0`,
stated for all `n ≥ 3` (where `a(n-2)` is in the sequence's range).

A python3 check: the formula reproduces the data and the recurrence holds for all `3 ≤ n < 400`.
The Lean kernel (`decide`) confirms `a 1, ..., a 14` against the 14 data terms.

Conventions: for `n ≥ 1`, `⌈(n-1)/2⌉ = n/2`, `⌊(n-1)/2⌋ = (n-1)/2`, and for `n ≥ 2`,
`⌈(n-2)/2⌉ = (n-1)/2`, `⌊(n-2)/2⌋ = (n-2)/2` (natural-number division). The recurrence is in `ℤ`.
-/

namespace OMA.S_oeis_a005559

/-- `a n = A005559(n)` for `n ≥ 1`. -/
def a (n : ℕ) : ℤ :=
  ((n + 1).choose (n / 2) * n.choose ((n - 1) / 2) : ℕ) -
    (if n ≤ 1 then 0 else ((n + 1).choose ((n - 1) / 2) * n.choose ((n - 2) / 2) : ℕ))

/-- Mathar's conjectured recurrence, for all `n ≥ 3`. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    -((n : ℤ) - 1) * (2 * n + 1) * (n + 4) * (n + 3) * a n
      + 4 * ((n : ℤ) + 1) * (2 * (n : ℤ) ^ 2 + 4 * n + 9) * a (n - 1)
      + 16 * (n : ℤ) * (n - 1) * (2 * n + 3) * (n + 1) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a005559
